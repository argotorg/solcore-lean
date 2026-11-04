import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConditionals
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LoopStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings

/-!
# Lambda views: trees

Edits, allocation and trees of expressions and bodies under a lambda view, with static typing and place lowering.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewEdits
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
/-! Finite paths through the typed source's actual occurrence references.
Cycles are permitted. A compiler edit is irrelevant to a body only when its
selected expression IDs are explicitly excluded from these paths. Ownership,
unique occurrence IDs and graph well-formedness alone do not give that fact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
open Frontend SourceInference
open CallableLambdaViewEdits

inductive Reaches (source : TypedSource) (roots : List NodeId) : NodeId → Prop where
  | root {id} (member : id ∈ roots) : Reaches source roots id
  | expression {id node child} (parent : Reaches source roots (.expression id))
      (found : source.lookupExpression? id = some node) (edge : child ∈ node.form.references) :
      Reaches source roots child
  | statement {id node child} (parent : Reaches source roots (.statement id))
      (found : source.lookupStatement? id = some node) (edge : child ∈ node.form.references) :
      Reaches source roots child

/-- Extend an already reached node by a finite path rooted at that node. -/
theorem Reaches.from_root {source : TypedSource} {roots : List NodeId} {root id : NodeId}
    (parent : Reaches source roots root) (path : Reaches source [root] id) :
    Reaches source roots id := by
  induction path with
  | @root id member =>
    have same : id = root := by simpa using member
    exact same ▸ parent
  | expression _ found edge ih => exact .expression ih found edge
  | statement _ found edge ih => exact .statement ih found edge

def Avoids (source : TypedSource) (roots : List NodeId) (changed : List ExpressionId) : Prop :=
  ∀ id ∈ changed, ¬Reaches source roots (.expression id)

theorem Avoids.fresh {source : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (avoids : Avoids source roots changed) {id : ExpressionId}
    (reached : Reaches source roots (.expression id)) : id ∉ changed :=
  fun member => avoids id member reached

theorem expression_lookup {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {id : ExpressionId} (reached : Reaches source roots (.expression id)) :
    source.lookupExpression? id = view.lookupExpression? id :=
  edited.unchanged id (avoids.fresh reached)

/-- Metadata views preserve reference topology even at edited headers. -/
theorem Reaches.metadata {source view : TypedSource} {roots : List NodeId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {id : NodeId} (reached : Reaches source roots id) : Reaches view roots id := by
  induction reached with
  | root member => exact .root member
  | expression _ found edge ih =>
    obtain ⟨node, selected, _, sameForm⟩ := metadata.symm.expression found
    exact .expression ih selected (sameForm ▸ edge)
  | statement _ found edge ih => exact .statement ih (metadata.symm.statement found) edge

theorem Avoids.view {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (metadata : LambdaMetadataViews.MetadataView source view) (avoids : Avoids source roots changed) :
    Avoids view roots changed :=
  fun id member reached => avoids id member (reached.metadata metadata.symm)

/-- The same finite reference path exists after the actual local edits.
No acyclicity assumption is introduced or derived. -/
theorem Reaches.transport {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {id : NodeId} (reached : Reaches source roots id) : Reaches view roots id := by
  induction reached with
  | root member => exact .root member
  | expression parent found edge ih =>
    exact .expression ih ((expression_lookup edited avoids parent).symm.trans found) edge
  | statement parent found edge ih =>
    exact .statement ih (edited.metadata.symm.statement found) edge

/-- Body expression lookups remain exact even when a path revisits a node. -/
theorem body_lookup {source view : TypedSource} {body : List StatementId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source (body.map NodeId.statement) changed)
    {id : ExpressionId} (reached : Reaches source (body.map NodeId.statement) (.expression id)) :
    source.lookupExpression? id = view.lookupExpression? id := expression_lookup edited avoids reached


/-- Source binders come from complete inputs, lambda forms and statement
metadata, all retained by the actual allocation metadata view. -/
theorem declaredBinders {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view) :
    SourceCoreDataPlaces.declaredBinders source = SourceCoreDataPlaces.declaredBinders view := by
  unfold SourceCoreDataPlaces.declaredBinders
  rw [metadata.inputs]
  congr 1
  have nodes := metadata.nodes
  generalize source.nodes = left at nodes ⊢
  generalize view.nodes = right at nodes ⊢
  induction nodes with
  | nil => rfl
  | cons node _ ih =>
    cases node with
    | expression sameId sameForm => simp only [List.flatMap_cons, sameForm, ih]
    | statement => simp only [List.flatMap_cons, ih]

theorem rootBinder {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view) (id : Resolved.LocalId) :
    SourceCoreDataPlaces.rootBinder source id = SourceCoreDataPlaces.rootBinder view id := by
  unfold SourceCoreDataPlaces.rootBinder
  rw [metadata.owner, declaredBinders metadata]

end Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewAllocations
/-! Allocation authentication depends on the original binder inventory and its
metadata view. Changing only expression annotations retains the actual emitted
allocation and its indexed ancestry snapshot, including capture references.
These static equalities do not reconstruct runtime allocation history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewAllocations
open Frontend SourceInference Core
abbrev Request := SourceCoreSourceCells.Request

/-- Reauthenticate the same receipt at an allocation-equivalent source view. -/
def emission {prepared : SourceCoreAllocationCodebook.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source)
    (receipt : SourceCoreAllocationCodebook.Emission prepared owner active request) :
    SourceCoreAllocationCodebook.Emission prepared owner active {request with source} :=
  {receipt with sourceExact := same.symm.trans receipt.sourceExact}

/-- The selected observed layout and all dynamic syntax stay identical. -/
def allocation {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source)
    (receipt : SourceCoreAllocationLayouts.Allocation prepared owner active request) :
    SourceCoreAllocationLayouts.Allocation prepared owner active {request with source} :=
  {receipt with authentication := emission same receipt.authentication}

/-- The emitter returns the same success or error after a view change. -/
theorem emission_status {prepared : SourceCoreAllocationCodebook.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source) :
    (SourceCoreAllocationCodebook.emitWithReceipt prepared owner active request).map (fun _ => ()) =
      (SourceCoreAllocationCodebook.emitWithReceipt prepared owner active {request with source}).map (fun _ => ()) := by
  unfold SourceCoreAllocationCodebook.emitWithReceipt
  simp (config := {zeta := false}) only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  simp only [same]
  repeat' first | rfl | split
  · rename_i yes no
    exact False.elim (no ⟨yes.1, yes.2.1, same.symm.trans yes.2.2.1, yes.2.2.2⟩)
  · rename_i no yes
    exact False.elim (no ⟨yes.1, yes.2.1, same.trans yes.2.2.1, yes.2.2.2⟩)


/-- Equality of the executable allocator, including rejection paths. -/
theorem allocate_eq {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source) :
    SourceCoreAllocationLayouts.allocate prepared owner active request =
      SourceCoreAllocationLayouts.allocate prepared owner active {request with source} := by
  have status := emission_status (prepared := prepared.codebook) (owner := owner) (active := active) same
  unfold SourceCoreAllocationLayouts.allocate SourceCoreAllocationLayouts.allocateWithReceipt
  cases left : SourceCoreAllocationCodebook.emitWithReceipt prepared.codebook owner active request <;>
    cases right : SourceCoreAllocationCodebook.emitWithReceipt prepared.codebook owner active {request with source} <;>
    simp only [left, right, Except.map, Except.error.injEq, reduceCtorEq] at status
  · cases status
    rfl
  · simp only [Except.mapError, bind, Except.bind, pure, Except.pure]
    split
    · rename_i absent
      split
      · rfl
      · rename_i entry present
        cases absent.symm.trans present
    · rename_i entry present
      split
      · rename_i absent
        cases present.symm.trans absent
      · rename_i other selected
        have equal : entry = other := Option.some.inj (present.symm.trans selected)
        subst other
        rfl


theorem allocator_eq {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource} (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source) :
    prepared.allocatorAt owner active onError request =
      prepared.allocatorAt owner active onError {request with source} :=
  congrArg (Except.mapError onError) (allocate_eq same)

/-- The real snapshot wrapper selects the same reference and emitted code.
The private annotation constructor is obtained only through its actual factory. -/
theorem annotation {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (view : LambdaMetadataViews.MetadataView request.source source)
    (receipt : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (prepared.allocatorAt owner active onError) request) :
    ∃ result : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (prepared.allocatorAt owner active onError) {request with source},
      result.original = receipt.original ∧ result.expression = receipt.expression := by
  have allocated : prepared.allocatorAt owner active onError {request with source} = .ok receipt.original :=
    (allocator_eq onError (CallableIndexedLambdaViewPrefix.sourceView_eq view)).symm.trans receipt.allocated
  cases found : SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt frame globals
      (prepared.allocatorAt owner active onError) {request with source} with
  | error error =>
    unfold SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt at found
    split at found
    · rename_i rejected
      cases allocated.symm.trans rejected
    · cases found
  | ok result =>
    have original := Except.ok.inj (result.allocated.symm.trans allocated)
    refine ⟨result, original, ?_⟩
    rw [result.exact, receipt.exact, original]
    congr 2
    simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex,
      SourceCoreCallableIndexedAllocationFrames.isNamedInput, view.inputs]
    rfl

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewAllocations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
/-! Static lexical body certificates survive local metadata views on a disjoint
body footprint. Expression certificates are transported at exactly the reached
child occurrences. This interface assumes no child execution or body meaning;
its concrete builtin-expression instantiation is a separate remaining step.
Real marker and snapshot receipts retain identical generated Core syntax. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
open Frontend SourceInference Core
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericLexicalStatements

private theorem statement_identity {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view) :
    GenericLexicalStatements.StatementSourceIdentity source view := by
  refine ⟨metadata.owner, metadata.inputs, metadata.roots, ?_⟩
  intro id
  cases found : source.lookupStatement? id with
  | some node => exact (metadata.symm.statement found).symm
  | none =>
    cases viewed : view.lookupStatement? id with
    | none => rfl
    | some node => have impossible := metadata.statement viewed; rw [found] at impossible; cases impossible

/-- Transport one actual finite statement certificate. The child interface is
static and restricted to the body's reached expression occurrences. -/
theorem transport {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (expressions : ∀ context scope id lowered, Reaches source roots (.expression id) →
      before context scope id lowered → after context scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source before context scope mode statements expected type code)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    Tree layouts owner active frame globals onError values view after context scope mode statements expected type code := by
  induction tree with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form => exact .returnUnit rest (edited.metadata.symm.statement found) form
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .returnValue rest (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType
      (expressions context scope expression lowered child value)
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .tail (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType
      (expressions context scope expression lowered child value)
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocated annotation same remaining ih =>
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    exact .uninitialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same) (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initializerFound sourceType initial allocated annotation same remaining ih =>
    have child : Reaches source roots (.expression initializer) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    exact .initialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .discard (edited.metadata.symm.statement found) form notTail
      ((expression_lookup edited avoids child).symm.trans expressionFound)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH restIH =>
    exact .block (edited.metadata.symm.statement found) form
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH restIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .ifThen (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))

  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerIH =>
    exact .terminalBlock (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (stops.transport (statement_identity edited.metadata)) (issued.transport (statement_identity edited.metadata))
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .terminalIf (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (thenStops.transport (statement_identity edited.metadata)) (elseStops.transport (statement_identity edited.metadata))
      (issued.transport (statement_identity edited.metadata))

/-- The body list itself supplies every statement root. -/
theorem body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (expressions : ∀ context scope id lowered, Reaches source (statements.map NodeId.statement) (.expression id) →
      before context scope id lowered → after context scope id lowered)
    (tree : Tree layouts owner active frame globals onError values source before context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values view after context scope mode statements expected type code :=
  transport edited avoids expressions tree (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))


/-- Recover the canonical body's static Tree from a compiler-view Tree.
Freshness is stated on the canonical body; the metadata topology theorem
transports it back to the actual view without assuming a tree-shaped graph. -/
theorem original {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (expressions : ∀ context scope id lowered, Reaches source (statements.map NodeId.statement) (.expression id) →
      before context scope id lowered → after context scope id lowered)
    (tree : Tree layouts owner active frame globals onError values view before context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values source after context scope mode statements expected type code := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  exact body reversed (avoids.view edited.metadata)
    (fun context scope id lowered reached => expressions context scope id lowered (reached.metadata edited.metadata.symm)) tree

/-- The literal-only instance closes the static child transformation using
complete lookup equality; even resolved numerals retain their evidence IDs.
The full recursive builtin expression instance is not asserted here. -/
theorem literals {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {solved : List SolvedRequirement} {context : SourceSemantics.Context} {scope : Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : Tree layouts owner active frame globals onError values source
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved source)
      context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values view
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved view)
      context scope mode statements expected type code := by
  apply body edited avoids ?_ tree
  intro context scope id lowered reached certificate
  obtain ⟨node, found, literal⟩ := certificate
  exact ⟨node, (expression_lookup edited avoids reached).symm.trans found, literal⟩

/-- A literal body extracted at the actual compiler view recovers the
canonical static certificate without equating the complete source records. -/
theorem literals_original {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {solved : List SolvedRequirement} {context : SourceSemantics.Context} {scope : Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : Tree layouts owner active frame globals onError values view
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved view)
      context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values source
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved source)
      context scope mode statements expected type code := by
  apply original edited avoids ?_ tree
  intro context scope id lowered reached certificate
  obtain ⟨node, found, literal⟩ := certificate
  exact ⟨node, (expression_lookup edited avoids reached).trans found, literal⟩

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewExpressionLeaves
/-! Static expression leaves retain their complete occurrence metadata under
local edits outside the reached body. Source binders are transported through
the actual metadata view, preserving lazy mapping encodings and raw types.
No independent source typing derivation or compiler equation is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewExpressionLeaves
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)

include edited avoids

theorem metadata {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId}
    {node : ExpressionNode} {type : Ty} (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.Metadata checked source id node type) :
    CompatibleExpressionReads.Metadata checked view id node type :=
  ⟨(expression_lookup edited avoids reached).symm.trans receipt.found,
    receipt.owner.trans edited.metadata.owner, receipt.requirements, receipt.coercions, receipt.projected⟩

theorem literal {solved : List SolvedRequirement} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered) :
    CompatibleExpressionLiterals.Certificate solved view id lowered := by
  obtain ⟨node, found, value⟩ := receipt
  exact ⟨node, (expression_lookup edited avoids reached).symm.trans found, value⟩

/-- The same read certificate keeps its declared binder, actual scope index,
quoted lazy default and emitted code. Only its source lookup receipts change. -/
def read {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.Certificate fuel values source scope id reason code) :
    CompatibleExpressionReads.Certificate fuel values view scope id reason code where
  node := receipt.node
  type := receipt.type
  binder := receipt.binder
  name := receipt.name
  declared := receipt.declared
  index := receipt.index
  metadata := metadata edited avoids reached receipt.metadata
  form := receipt.form
  binderOwner := receipt.binderOwner.trans edited.metadata.owner
  slot := receipt.slot
  declaration := (rootBinder edited.metadata receipt.binder).symm.trans receipt.declaration
  emitted := receipt.emitted

theorem read_binding {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    {context : SourceSemantics.Context} (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
    (binding : CompatibleExpressionReads.StaticBinding receipt context) :
    CompatibleExpressionReads.StaticBinding (read edited avoids reached receipt) context :=
  ⟨binding.declared, binding.occurrence⟩

theorem loweredRead {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
    CompatibleExpressionReads.LoweredRead fuel values view context reasonAt scope id lowered := by
  obtain ⟨certificate, type, binding⟩ := receipt
  exact ⟨read edited avoids reached certificate, type, read_binding edited avoids reached certificate binding⟩

theorem proxy {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered) :
    CompatibleExpressionProxies.Certificate values view scope id lowered := by
  cases receipt with
  | proxy header =>
    exact .proxy ⟨metadata edited avoids reached header.metadata, header.form, header.sourceType,
      header.identity, header.original, header.registered⟩

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewExpressionLeaves
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewScalarTrees
/-! Exact static scalar-expression trees across local compiler views. Every
recursive step follows the original node's actual references; a disjoint edit
therefore retains raw types, evidence identities, operator profiles and code.
This transports certificates, not arbitrary source typing or compiler actions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewScalarTrees
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem products {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionProducts.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | literal receipt => intro reached; exact .literal (CallableLambdaViewExpressionLeaves.literal edited avoids reached receipt)
  | read receipt => intro reached; exact .read (CallableLambdaViewExpressionLeaves.loweredRead edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)

theorem primitives {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionPrimitives.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | product tree => intro reached; exact .product (products edited avoids tree reached)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (firstIH leftReached) (secondIH rightReached)

theorem conditionals {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConditionals.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | primitive tree => intro reached; exact .primitive (primitives edited avoids tree reached)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

/-- Recover an original scalar tree from the actual compiler view. The same
canonical reachability condition suffices because metadata views retain edges. -/
theorem conditionals_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionConditionals.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact conditionals reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewScalarTrees
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewDataTrees
/-! Constructor and member certificates across local compiler views. Complete
reached lookups preserve the original instantiation, ordered payload types,
registry header, native layout and generated child code. No new source typing
or compiler acceptance is inferred from this static transport. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewDataTrees
open Core Frontend SourceInference DataPatternValues
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem header {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {tag : ConstructorId} {word : Word} {codes : List SourceCoreBasic.LoweredExpr}
    (reached : Reaches source roots (.expression id))
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag word codes) :
    CompatibleExpressionConstructors.Header values view id node instantiation tag word codes :=
  {receipt with metadata := CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt.metadata}

theorem nodes {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionConstructors.Nodes source ids types codes)
    (reached : ∀ id, id ∈ ids → Reaches source roots (.expression id)) :
    CompatibleExpressionConstructors.Nodes view ids types codes := by
  induction ids generalizing types codes with
  | nil => cases receipt; exact .nil
  | cons id ids ih =>
    cases types with
    | nil => cases receipt; exact .nil
    | cons type types =>
      cases receipt with
      | cons head tail =>
        obtain ⟨node, found, rawType⟩ := head
        exact .cons ⟨node, (expression_lookup edited avoids (reached id (by simp))).symm.trans found, rawType⟩
          (ih tail (fun child member => reached child (by simp [member])))

omit edited avoids in
theorem constructor_children {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    (reached : Reaches source roots (.expression id)) (found : source.lookupExpression? id = some node)
    (form : node.form = .constructor instantiation ids) :
    ∀ child, child ∈ ids → Reaches source roots (.expression child) := by
  intro child member
  exact .expression reached found (by simp [form, ExpressionForm.references, member])

theorem constructors {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConstructors.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewScalarTrees.conditionals edited avoids tree reached)
  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children ih =>
    intro reached
    have childReached := constructor_children reached receipt.metadata.found form
    exact .constructor (header edited avoids reached receipt) form valid count
      (nodes edited avoids nodeReceipt childReached)
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))

theorem members {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionMembers.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (constructors edited avoids tree reached)
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (ih baseReached)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewDataTrees
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewRecursiveTrees
/-! Static source congruence for the recursive constructor/member expression
grammar. Recursion follows every actual child reference, including all lazy
branches, and retains exactly the original code and metadata receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewRecursiveTrees
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem recursive {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionRecursive.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewDataTrees.members edited avoids tree reached)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (ih baseReached)

/-- Recover an original recursive tree from the actual compiler view. The same
canonical reachability condition suffices because metadata views retain edges. -/
theorem recursive_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionRecursive.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact recursive reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewRecursiveTrees
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewIndexedTrees
/-! Mapping index and typed recursive trees across local compiler views.
The exact prepared comparator, default-producing reads, raw key/result types
and actual child code are retained. Reachability constrains edits; typing and
accepted compiler equations remain independent static obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewIndexedTrees
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem header {id base : ExpressionId} {node baseNode : ExpressionNode}
    {layout : OrderedMapping.Layout} {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (reached : Reaches source roots (.expression id)) (baseReached : Reaches source roots (.expression base))
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second) :
    CompatibleExpressionIndices.Header values view id base node baseNode layout comparison first second :=
  {receipt with metadata := CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt.metadata
                baseMetadata := CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached receipt.baseMetadata}

theorem indices {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionIndices.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionIndices.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewDataTrees.members edited avoids tree reached)
  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType scalar (firstIH baseReached) (secondIH keyReached)

theorem typed {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionTyped.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionTyped.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewRecursiveTrees.recursive edited avoids tree reached)
  | proxy receipt => intro reached; exact .proxy (CallableLambdaViewExpressionLeaves.proxy edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (ih baseReached)

  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType scalar (firstIH baseReached) (secondIH keyReached)

theorem general {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionGeneral.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewRecursiveTrees.recursive edited avoids tree reached)
  | proxy receipt => intro reached; exact .proxy (CallableLambdaViewExpressionLeaves.proxy edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (ih baseReached)

  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType (firstIH baseReached) (secondIH keyReached)

theorem indices_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionIndices.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionIndices.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact indices reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

theorem typed_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionTyped.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionTyped.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact typed reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

theorem general_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionGeneral.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact general reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewIndexedTrees
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
/-! Exact builtin expression certificates across local lambda metadata views.
Every recursive child keeps its original raw type, ordered operand code and
contracted callee. Source typing, syntax and compiler acceptance remain separate
static obligations; reachability supplies complete node equality. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

theorem builtins {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Tree fuel values view context solved reasonAt scope id lowered := by
  revert reached
  induction tree with
  | fragment tree => intro reached; exact .fragment (CallableLambdaViewIndexedTrees.general edited avoids tree reached)
  | proxy receipt => intro reached; exact .proxy (CallableLambdaViewExpressionLeaves.proxy edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (ih baseReached)

  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType firstTree secondTree firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (CallableLambdaViewIndexedTrees.header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType (firstIH baseReached) (secondIH keyReached)

  | @builtin id callee arguments function node codes identity contract unknown receipt form sourceType count nodes nativeTypes children ih =>
    intro reached
    have childReached : ∀ child, child ∈ arguments → Reaches source roots (.expression child) := by
      intro child member
      exact .expression reached receipt.found (by simp [form, ExpressionForm.references, member])
    exact .builtin (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form sourceType count
      (CallableLambdaViewDataTrees.nodes edited avoids nodes childReached) nativeTypes
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))

theorem builtins_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionBuiltins.Tree fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact builtins reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree
/-! Concrete builtin lexical certificates across local lambda views.
The finite body keeps its source contexts, actual marker/snapshot allocator
receipts and exact Core code. Reached child transport is closed by the builtin
expression grammar, without a child execution or static transport premise.
Canonical source typing, syntax and compiler acceptance remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {source view : TypedSource} {changed : List ExpressionId}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

/-- Let, block, conditional, discard, return, tail and Unit certificates retain
exact code; the same ordered builtin child certificates hold at the view. -/
theorem body (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source
      solved reasonAt context scope mode statements expected type code) :
    BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values view
      solved reasonAt context scope mode statements expected type code := by
  apply CallableLambdaViewBodyTree.body edited avoids ?_ tree
  intro context scope id lowered reached child
  exact CallableLambdaViewBuiltinTrees.builtins edited avoids child reached

/-- Recover the canonical body certificate from the actual compiler view.
Only the static Tree is recovered; no canonical typing or acceptance is asserted. -/
theorem original (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values view
      solved reasonAt context scope mode statements expected type code) :
    BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source
      solved reasonAt context scope mode statements expected type code := by
  apply CallableLambdaViewBodyTree.original edited avoids ?_ tree
  intro context scope id lowered reached child
  exact CallableLambdaViewBuiltinTrees.builtins_original edited avoids child reached

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
/-! All thirteen independent source typing judgments transport along exact
reached nodes of a local compiler view. Recursion follows finite typing
proofs, including lambda bodies, calls, places, loops and match arms.
The source graph may contain cycles. Compiler acceptance, static lowering
trees and runtime history remain separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
open Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

/-- Every occurrence referenced by a typing judgment is in the retained
reference closure. The order and repeated references remain unchanged. -/
def Within (source : TypedSource) (roots ids : List NodeId) : Prop :=
  ∀ id ∈ ids, Reaches source roots id

@[simp] private theorem within_nil (source : TypedSource) (roots : List NodeId) :
    Within source roots [] := by intro id member; cases member
@[simp] private theorem within_cons {source : TypedSource} {roots : List NodeId}
    {id : NodeId} {ids : List NodeId} :
    Within source roots (id :: ids) ↔ Reaches source roots id ∧ Within source roots ids := by
  constructor
  · intro all; exact ⟨all id (by simp), fun child member => all child (by simp [member])⟩
  · rintro ⟨head, tail⟩ child member
    rcases List.mem_cons.mp member with same | member
    · subst child; exact head
    · exact tail child member
@[simp] private theorem within_append {source : TypedSource} {roots first second : List NodeId} :
    Within source roots (first ++ second) ↔ Within source roots first ∧ Within source roots second := by
  simp only [Within, List.mem_append, or_imp, forall_and]
@[simp] private theorem within_flatMap_cons {α : Type} {source : TypedSource} {roots : List NodeId}
    {f : α → List NodeId} {head : α} {tail : List α} :
    Within source roots ((head :: tail).flatMap f) ↔
      Within source roots (f head) ∧ Within source roots (tail.flatMap f) := by
  simp only [List.flatMap_cons, within_append]

theorem Within.view {source view : TypedSource} {roots ids : List NodeId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (within : Within source roots ids) : Within view roots ids :=
  fun id member => (within id member).metadata metadata

private theorem expression_contains {source view : TypedSource} {roots : List NodeId}
    {changed : List ExpressionId} (edited : LocalView source view changed)
    (avoids : Avoids source roots changed) (unique : NodeOccurrencesUnique source)
    {id : ExpressionId} {node : ExpressionNode} (reached : Reaches source roots (.expression id))
    (contains : ContainsExpression source id node) : ContainsExpression view id node :=
  lookupExpression?_sound ((expression_lookup edited avoids reached).symm.trans
    (lookupExpression?_complete unique contains))

private theorem statement_contains {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) (unique : NodeOccurrencesUnique source)
    {id : StatementId} {node : StatementNode} (contains : ContainsStatement source id node) :
    ContainsStatement view id node :=
  lookupStatement?_sound (edited.metadata.symm.statement (lookupStatement?_complete unique contains))

private theorem expression_children {source : TypedSource} {roots : List NodeId}
    (unique : NodeOccurrencesUnique source) {id : ExpressionId} {node : ExpressionNode}
    (contains : ContainsExpression source id node) (reached : Reaches source roots (.expression id)) :
    Within source roots node.form.references :=
  fun _ member => .expression reached (lookupExpression?_complete unique contains) member

private theorem statement_children {source : TypedSource} {roots : List NodeId}
    (unique : NodeOccurrencesUnique source) {id : StatementId} {node : StatementNode} {form : StatementForm}
    (contains : ContainsStatement source id node) (same : node.form = form)
    (reached : Reaches source roots (.statement id)) : Within source roots form.references := by
  intro child member
  exact .statement reached (lookupStatement?_complete unique contains) (same ▸ member)

private theorem binder {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) {context final : Context} {item : TypedBinder}
    (extended : BinderExtends source.owner context item final) : BinderExtends view.owner context item final := by
  rw [← edited.metadata.owner]; exact extended
private theorem binders {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) {context final : Context} {items : List TypedBinder}
    (extended : BindersExtend source.owner context items final) : BindersExtend view.owner context items final := by
  rw [← edited.metadata.owner]; exact extended
private theorem monoBinders {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) {context final : Context} {items : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend source.owner context items types final) :
    MonoBindersExtend view.owner context items types final := by
  rw [← edited.metadata.owner]; exact extended

private theorem declaration_callee {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed) (unique : NodeOccurrencesUnique source)
    {context : Context} {id : ExpressionId} {instantiation : DeclarationInstantiation}
    (reached : Reaches source roots (.expression id))
    (typed : DirectDeclarationCalleeValid context source id instantiation) :
    DirectDeclarationCalleeValid context view id instantiation := by
  cases typed with
  | intro contains form valid raw requirements coercions =>
    exact .intro (expression_contains edited avoids unique reached contains) form valid raw requirements coercions

private theorem builtin_callee {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed) (unique : NodeOccurrencesUnique source)
    {id : ExpressionId} {function : BuiltinFunctionId} (reached : Reaches source roots (.expression id))
    (typed : DirectBuiltinCalleeValid source id function) : DirectBuiltinCalleeValid view id function := by
  cases typed with
  | intro contains form raw requirements coercions =>
    exact .intro (expression_contains edited avoids unique reached contains) form raw requirements coercions

section Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

local macro "transport_static" "(" recursor:term "," before:term "," after:term ","
    roots:term "," edited:term "," avoids:term "," unique:term "," typing:term ")" : term =>
  `($recursor (source := $before)
    (motive_1 := fun context id type _ => Reaches $before $roots (.expression id) → ExpressionHasType $after context id type)
    (motive_2 := fun context form raw plan _ => Within $before $roots form.references → ExpressionFormHasRawType $after context form raw plan)
    (motive_3 := fun context ids types _ => Within $before $roots (ids.map NodeId.expression) → ExpressionsHaveTypes $after context ids types)
    (motive_4 := fun context initial projections final _ => Within $before $roots (projections.flatMap PlaceProjection.references) → SourceProjectionsHaveType $after context initial projections final)
    (motive_5 := fun context place type _ => Within $before $roots place.references → SourcePlaceHasType $after context place type)
    (motive_6 := fun context assignment operator value _ => Within $before $roots (assignment.references ++ [.expression value]) → SourceAssignmentHasType $after context assignment operator value)
    (motive_7 := fun context assignment _ => Within $before $roots assignment.references → SourceBitNotAssignmentValid $after context assignment)
    (motive_8 := fun control context id final facts _ => Reaches $before $roots (.statement id) → StatementHasType $after control context id final facts)
    (motive_9 := fun control context ids final facts _ => Within $before $roots (ids.map NodeId.statement) → StatementsHaveType $after control context ids final facts)
    (motive_10 := fun control context item final _ => Within $before $roots item.references → ForItemHasType $after control context item final)
    (motive_11 := fun control context items final _ => Within $before $roots (items.flatMap ForItemForm.references) → ForItemsHaveType $after control context items final)
    (motive_12 := fun control context type arm facts _ => Within $before $roots arm.references → MatchCaseHasType $after control context type arm facts)
    (motive_13 := fun control context type arms facts _ => Within $before $roots (arms.flatMap TypedMatchCase.references) → MatchCasesHaveType $after control context type arms facts)
    (fun contains _ raw wfRaw wfType requirements ih reached =>
      .intro (expression_contains $edited $avoids $unique reached contains)
        (ih (expression_children $unique contains reached)) raw wfRaw wfType requirements)
    (fun valid _ => .literal valid)
    (fun valid _ => .integerLiteral valid)
    (fun valid _ => .reference valid)
    (fun _ ih h => .group (ih (by simpa [ExpressionForm.references] using h)))
    (fun _ ih h => .tuple (ih h))
    (fun _ operator ih h => .unary (ih (by simpa [ExpressionForm.references] using h)) operator)
    (fun _ _ operator left right h => by
      simp only [ExpressionForm.references, within_cons, within_nil, and_true] at h
      exact .binary (left h.1) (right h.2) operator)
    (fun _ _ _ condition first second h => by
      simp only [ExpressionForm.references, within_cons, within_nil, and_true] at h
      exact .conditional (condition h.1) (first h.2.1) (second h.2.2))
    (fun names extended _ completes ih h => .lambda names (monoBinders $edited extended) (ih h) completes)
    (fun callee application _ ih h => by
      simp only [ExpressionForm.references, within_cons] at h
      exact .directCall (declaration_callee $edited $avoids $unique h.1 callee) application (ih h.2))
    (fun callee _ ih h => by
      simp only [ExpressionForm.references, within_cons] at h
      exact .builtinCall (builtin_callee $edited $avoids $unique h.1 callee) (ih h.2))
    (fun _ _ application callee arguments h => by
      simp only [ExpressionForm.references, within_cons] at h
      exact .indirectCall (callee h.1) (arguments h.2) application)
    (fun valid _ ih h => .constructor valid (ih h))
    (fun _ selected ih h => .member (ih (by simpa [ExpressionForm.references] using h)) selected)
    (fun valid _ => .proxy valid)
    (fun _ _ first second h => by
      simp only [ExpressionForm.references, within_cons, within_nil, and_true] at h
      exact .index (first h.1) (second h.2))
    (fun _ _ => .nil _)
    (fun _ _ head tail h => by
      simp only [List.map_cons, within_cons] at h
      exact .cons (head h.1) (tail (by simpa only [List.map_cons, within_cons] using h.2)))
    (fun type _ => .nil type)
    (fun _ _ key rest h => by
      simp only [within_flatMap_cons, PlaceProjection.references, within_cons, within_nil, and_true] at h
      exact .index (key h.1) (rest h.2))
    (fun selected _ ih h => by
      simp only [within_flatMap_cons, PlaceProjection.references, within_nil, true_and] at h
      exact .member selected (ih h))
    (fun root _ same ih h => .intro root (ih h) same)
    (fun _ _ requirements target value h => by
      simp only [within_append, within_cons, within_nil, and_true] at h
      exact .equal (target h.1) (value h.2) requirements)
    (fun operator _ _ requirements target value h => by
      simp only [within_append, within_cons, within_nil, and_true] at h
      exact .wordCompound operator (target h.1) (value h.2) requirements)
    (fun _ requirements ih h => .intro (ih h) requirements)
    (fun contains form mono generalizes extended type _ =>
      .letUninitialized (statement_contains $edited $unique contains) form mono generalizes (binder $edited extended) type)
    (fun contains form _ mono generalizes extended type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.map_some, Option.toList_some, within_cons, within_nil, and_true] at reached
      exact .letInitialized (statement_contains $edited $unique contains) form (ih reached) mono generalizes (binder $edited extended) type)
    (fun contains form poly wellFormed generalizes _ extended type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.map_some, Option.toList_some, within_cons, within_nil, and_true] at reached
      exact .letInitializedGeneralized (statement_contains $edited $unique contains) form poly wellFormed generalizes (ih reached) (binder $edited extended) type)
    (fun contains form raw type _ => .returnUnit (statement_contains $edited $unique contains) form raw type)
    (fun contains form _ type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.map_some, Option.toList_some, within_cons, within_nil, and_true] at reached
      exact .returnValue (statement_contains $edited $unique contains) form (ih reached) type)
    (fun contains form _ type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_cons, within_nil, and_true] at reached
      exact .expressionValue (statement_contains $edited $unique contains) form (ih reached) type)
    (fun contains form _ type ih h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_cons, within_nil, and_true] at reached
      exact .expressionDiscard (statement_contains $edited $unique contains) form (ih reached) type)
    (fun contains form _ type ih h =>
      .assignValue (statement_contains $edited $unique contains) form (ih (statement_children $unique contains form h)) type)
    (fun contains form _ type ih h =>
      .assignBitNot (statement_contains $edited $unique contains) form (ih (statement_children $unique contains form h)) type)
    (fun contains form _ _ type condition first h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_append, within_cons, within_nil, and_true] at reached
      exact .ifWithoutElse (statement_contains $edited $unique contains) form (condition reached.1.1) (first reached.1.2) type)
    (fun contains form _ _ _ type condition first second h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, Option.getD_some, within_append, within_cons, within_nil, and_true] at reached
      exact .ifWithElse (statement_contains $edited $unique contains) form (condition reached.1.1) (first reached.1.2) (second reached.2) type)
    (fun contains form _ type ih h =>
      .block (statement_contains $edited $unique contains) form (ih (statement_children $unique contains form h)) type)
    (fun contains form default _ _ requirements exhaustive merged type scrutinee arms h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, MatchResolution.references, within_append, within_cons, within_nil, and_true] at reached
      exact .matchWithoutDefault (statement_contains $edited $unique contains) form default (scrutinee reached.1.1) (arms reached.1.2) requirements exhaustive merged type)
    (fun contains form default _ _ _ requirements merged type scrutinee arms fallback h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, MatchResolution.references, default, Option.getD_some, within_append, within_cons, within_nil, and_true] at reached
      exact .matchWithDefault (statement_contains $edited $unique contains) form default (scrutinee reached.1.1) (arms reached.1.2) (fallback reached.2) requirements merged type)
    (fun contains form _ _ _ _ type initial condition body post h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_append, within_cons, within_nil, and_true] at reached
      exact .forLoop (statement_contains $edited $unique contains) form (initial reached.1.1.1) (condition reached.1.1.2) (body reached.2) (post reached.1.2) type)
    (fun contains form _ _ type condition body h => by
      have reached := statement_children $unique contains form h
      simp only [StatementForm.references, within_cons] at reached
      exact .whileLoop (statement_contains $edited $unique contains) form (condition reached.1) (body reached.2) type)
    (fun contains form allowed type _ => .breakStmt (statement_contains $edited $unique contains) form allowed type)
    (fun contains form allowed type _ => .continueStmt (statement_contains $edited $unique contains) form allowed type)
    (fun _ _ _ => .nil _ _)
    (fun _ ih h => .singleton (ih (by simpa using h)))
    (fun _ _ head tail h => by
      simp only [List.map_cons, within_cons] at h
      exact .cons (head h.1) (tail (by simpa only [List.map_cons, within_cons] using h.2)))
    (fun mono generalizes extended _ => .letUninitialized mono generalizes (binder $edited extended))
    (fun _ mono generalizes extended ih h =>
      .letInitialized (ih (by simpa [ForItemForm.references] using h)) mono generalizes (binder $edited extended))
    (fun poly wellFormed generalizes _ extended ih h =>
      .letInitializedGeneralized poly wellFormed generalizes (ih (by simpa [ForItemForm.references] using h)) (binder $edited extended))
    (fun _ ih h => .expression (ih (by simpa [ForItemForm.references] using h)))
    (fun _ ih h => .assignValue (ih h))
    (fun _ ih h => .assignBitNot (ih h))
    (fun _ _ _ => .nil _ _)
    (fun _ _ head tail h => by
      simp only [within_flatMap_cons] at h
      exact .cons (head h.1) (tail h.2))
    (fun pattern extended _ ih h => .intro pattern (binders $edited extended) (ih h))
    (fun _ _ _ _ => .nil _ _ _)
    (fun _ _ head tail h => by
      simp only [within_flatMap_cons] at h
      exact .cons (head h.1) (tail h.2))
    $typing)

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  (unique : NodeOccurrencesUnique source)

include edited avoids unique in
theorem expression {context : Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typed : ExpressionHasType source context id type) (reached : Reaches source roots (.expression id)) :
    ExpressionHasType view context id type :=
  transport_static(ExpressionHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem form {context : Context} {form : ExpressionForm} {type : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (typed : ExpressionFormHasRawType source context form type plan) (reached : Within source roots form.references) :
    ExpressionFormHasRawType view context form type plan :=
  transport_static(ExpressionFormHasRawType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem expressions {context : Context} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types) (reached : Within source roots (ids.map NodeId.expression)) :
    ExpressionsHaveTypes view context ids types :=
  transport_static(ExpressionsHaveTypes.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem projections {context : Context} {initial final : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType source context initial projections final) (reached : Within source roots (projections.flatMap PlaceProjection.references)) :
    SourceProjectionsHaveType view context initial projections final :=
  transport_static(SourceProjectionsHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem place {context : Context} {place : PlaceResolution} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context place type) (reached : Within source roots place.references) :
    SourcePlaceHasType view context place type :=
  transport_static(SourcePlaceHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem assignment {context : Context} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {value : ExpressionId}
    (typed : SourceAssignmentHasType source context assignment operator value) (reached : Within source roots (assignment.references ++ [.expression value])) :
    SourceAssignmentHasType view context assignment operator value :=
  transport_static(SourceAssignmentHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem bitNot {context : Context} {assignment : AssignmentResolution}
    (typed : SourceBitNotAssignmentValid source context assignment) (reached : Within source roots assignment.references) :
    SourceBitNotAssignmentValid view context assignment :=
  transport_static(SourceBitNotAssignmentValid.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem statement {control : ControlContext} {context final : Context} {id : StatementId} {facts : StatementFacts}
    (typed : StatementHasType source control context id final facts) (reached : Reaches source roots (.statement id)) :
    StatementHasType view control context id final facts :=
  transport_static(StatementHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem statements {control : ControlContext} {context final : Context} {ids : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context ids final facts) (reached : Within source roots (ids.map NodeId.statement)) :
    StatementsHaveType view control context ids final facts :=
  transport_static(StatementsHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem forItem {control : ControlContext} {context final : Context} {item : ForItemForm}
    (typed : ForItemHasType source control context item final) (reached : Within source roots item.references) :
    ForItemHasType view control context item final :=
  transport_static(ForItemHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem forItems {control : ControlContext} {context final : Context} {items : List ForItemForm}
    (typed : ForItemsHaveType source control context items final) (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ForItemsHaveType view control context items final :=
  transport_static(ForItemsHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem matchCase {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arm : TypedMatchCase} {facts : BodyFacts}
    (typed : MatchCaseHasType source control context type arm facts) (reached : Within source roots arm.references) :
    MatchCaseHasType view control context type arm facts :=
  transport_static(MatchCaseHasType.rec, source, view, roots, edited, avoids, unique, typed) reached

include edited avoids unique in
theorem matchCases {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arms : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type arms facts) (reached : Within source roots (arms.flatMap TypedMatchCase.references)) :
    MatchCasesHaveType view control context type arms facts :=
  transport_static(MatchCasesHaveType.rec, source, view, roots, edited, avoids, unique, typed) reached

/-- The reverse transport uses the same canonical exclusion of edits.
The metadata receipt carries occurrence uniqueness and graph paths to the view. -/
private theorem reverse_view {source view : TypedSource} {changed : List ExpressionId}
    (edited : LocalView source view changed) : LocalView view source changed :=
  ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩

include edited avoids unique in
theorem expression_original {context : Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typed : ExpressionHasType view context id type) (reached : Reaches source roots (.expression id)) :
    ExpressionHasType source context id type :=
  expression (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.metadata edited.metadata)

include edited avoids unique in
theorem form_original {context : Context} {form : ExpressionForm} {type : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (typed : ExpressionFormHasRawType view context form type plan) (reached : Within source roots form.references) :
    ExpressionFormHasRawType source context form type plan :=
  CallableLambdaViewStaticTyping.form (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem expressions_original {context : Context} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes view context ids types) (reached : Within source roots (ids.map NodeId.expression)) :
    ExpressionsHaveTypes source context ids types :=
  expressions (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem projections_original {context : Context} {initial final : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType view context initial projections final) (reached : Within source roots (projections.flatMap PlaceProjection.references)) :
    SourceProjectionsHaveType source context initial projections final :=
  CallableLambdaViewStaticTyping.projections (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem place_original {context : Context} {place : PlaceResolution} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType view context place type) (reached : Within source roots place.references) :
    SourcePlaceHasType source context place type :=
  CallableLambdaViewStaticTyping.place (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem assignment_original {context : Context} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {value : ExpressionId}
    (typed : SourceAssignmentHasType view context assignment operator value) (reached : Within source roots (assignment.references ++ [.expression value])) :
    SourceAssignmentHasType source context assignment operator value :=
  CallableLambdaViewStaticTyping.assignment (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem bitNot_original {context : Context} {assignment : AssignmentResolution}
    (typed : SourceBitNotAssignmentValid view context assignment) (reached : Within source roots assignment.references) :
    SourceBitNotAssignmentValid source context assignment :=
  bitNot (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem statement_original {control : ControlContext} {context final : Context} {id : StatementId} {facts : StatementFacts}
    (typed : StatementHasType view control context id final facts) (reached : Reaches source roots (.statement id)) :
    StatementHasType source control context id final facts :=
  statement (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.metadata edited.metadata)

include edited avoids unique in
theorem statements_original {control : ControlContext} {context final : Context} {ids : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType view control context ids final facts) (reached : Within source roots (ids.map NodeId.statement)) :
    StatementsHaveType source control context ids final facts :=
  statements (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem forItem_original {control : ControlContext} {context final : Context} {item : ForItemForm}
    (typed : ForItemHasType view control context item final) (reached : Within source roots item.references) :
    ForItemHasType source control context item final :=
  forItem (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem forItems_original {control : ControlContext} {context final : Context} {items : List ForItemForm}
    (typed : ForItemsHaveType view control context items final) (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ForItemsHaveType source control context items final :=
  forItems (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem matchCase_original {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arm : TypedMatchCase} {facts : BodyFacts}
    (typed : MatchCaseHasType view control context type arm facts) (reached : Within source roots arm.references) :
    MatchCaseHasType source control context type arm facts :=
  matchCase (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

include edited avoids unique in
theorem matchCases_original {control : ControlContext} {context : Context} {type : TypeSystem.Ty} {arms : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType view control context type arms facts) (reached : Within source roots (arms.flatMap TypedMatchCase.references)) :
    MatchCasesHaveType source control context type arms facts :=
  matchCases (reverse_view edited) (avoids.view edited.metadata)
    (edited.metadata.unique unique) typed (reached.view edited.metadata)

end Transport

/-- Whole body typing, without a restricted expression syntax or a lowering
Tree. All raw types, lexical output contexts and control facts are retained. -/
theorem body_iff {source view : TypedSource} {body : List StatementId} {changed : List ExpressionId}
    (edited : LocalView source view changed)
    (avoids : Avoids source (body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : Context} {facts : BodyFacts} :
    StatementsHaveType source control context body final facts ↔
      StatementsHaveType view control context body final facts :=
  ⟨fun typed => statements edited avoids unique typed (fun _ member => .root member),
   fun typed => statements_original edited avoids unique typed (fun _ member => .root member)⟩

theorem expression_iff {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source) {context : Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (reached : Reaches source roots (.expression id)) :
    ExpressionHasType source context id type ↔ ExpressionHasType view context id type :=
  ⟨fun typed => expression edited avoids unique typed reached,
   fun typed => expression_original edited avoids unique typed reached⟩

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
/-! Independent source typing and lexical syntax across a local lambda view.
Complete reached expression nodes are preserved; owner, inputs and statements
come from the actual metadata receipt. The ordinary builtin expression grammar
closes the recursive typing obligations. No runtime meaning or compiler
equation is assumed, and edited reachable headers are explicitly excluded. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
open Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

private theorem statement_identity {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view) :
    GenericLexicalStatements.StatementSourceIdentity source view := by
  refine ⟨metadata.owner, metadata.inputs, metadata.roots, ?_⟩
  intro id
  cases found : source.lookupStatement? id with
  | some node => exact (metadata.symm.statement found).symm
  | none =>
    cases viewed : view.lookupStatement? id with
    | none => rfl
    | some node => have impossible := metadata.statement viewed; rw [found] at impossible; cases impossible

private def BodyFree : ExpressionForm → Prop
  | .lambda _ _ _ => False
  | .call _ _ (.declaration _) => False
  | .call _ _ (.indirect _) => False
  | _ => True

private def typingChildren : ExpressionForm → List ExpressionId
  | .group inner => [inner]
  | .tuple ids => ids
  | .unary _ operand => [operand]
  | .binary first _ second => [first, second]
  | .conditional condition first second => [condition, first, second]
  | .call _ arguments (.builtinFunction _) => arguments
  | .constructor _ arguments => arguments
  | .member base _ _ => [base]
  | .index base key => [base, key]
  | _ => []

private theorem atomic_free {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    BodyFree form := by cases atomic <;> trivial
private theorem atomic_children {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    typingChildren form = [] := by cases atomic <;> rfl

private def TypedAt (source view : TypedSource) (id : ExpressionId) : Prop :=
  ∀ context type, ExpressionHasType source context id type → ExpressionHasType view context id type

private theorem types {source view : TypedSource} {context : Context}
    {ids : List ExpressionId} {result : List TypeSystem.Ty}
    (children : ∀ id ∈ ids, TypedAt source view id)
    (typed : ExpressionsHaveTypes source context ids result) :
    ExpressionsHaveTypes view context ids result := by
  cases typed with
  | nil => exact .nil _
  | @cons context id ids type result head tail =>
    exact .cons (children id (by simp) _ _ head)
      (types (fun id member => children id (List.mem_cons_of_mem _ member)) tail)
termination_by ids.length

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  (unique : NodeOccurrencesUnique source)

include edited avoids unique in
private theorem step {id : ExpressionId} {node : ExpressionNode}
    (reached : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node) (ordinary : BodyFree node.form)
    (children : ∀ child ∈ typingChildren node.form, TypedAt source view child) :
    TypedAt source view id := by
  intro context type typed
  cases typed with
  | @intro _ _ selected raw plan contains formType rawType rawWellFormed typeWellFormed requirements =>
    have same : selected = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst selected
    apply ExpressionHasType.intro
      (lookupExpression?_sound ((expression_lookup edited avoids reached).symm.trans found))
      ?_ rawType rawWellFormed typeWellFormed requirements
    generalize shape : node.form = form at formType children ordinary ⊢
    revert children ordinary
    cases formType with
    | literal valid => intros; exact .literal valid
    | integerLiteral valid => intros; exact .integerLiteral valid
    | reference valid => intros; exact .reference valid
    | group typed => intro children _; exact .group (children _ (by simp [typingChildren]) _ _ typed)
    | tuple typed => intro children _; exact .tuple (types (by simpa only [typingChildren] using children) typed)
    | unary typed operator => intro children _; exact .unary (children _ (by simp [typingChildren]) _ _ typed) operator
    | binary first second operator =>
      intro children _
      exact .binary (children _ (by simp [typingChildren]) _ _ first)
        (children _ (by simp [typingChildren]) _ _ second) operator
    | conditional condition first second =>
      intro children _
      exact .conditional (children _ (by simp [typingChildren]) _ _ condition)
        (children _ (by simp [typingChildren]) _ _ first)
        (children _ (by simp [typingChildren]) _ _ second)
    | lambda => intro _ ordinary; cases ordinary
    | directCall => intro _ ordinary; cases ordinary
    | @builtinCall _ callee arguments function calleeValid typed =>
      intro children _
      have calleeReached : Reaches source roots (.expression callee) :=
        .expression reached found (by simp [shape, ExpressionForm.references])
      cases calleeValid with
      | intro contains form sameType sameRequirements sameCoercions =>
        exact .builtinCall
          (.intro (lookupExpression?_sound ((expression_lookup edited avoids calleeReached).symm.trans
            (lookupExpression?_complete unique contains))) form sameType sameRequirements sameCoercions)
          (types (by simpa only [typingChildren] using children) typed)
    | indirectCall => intro _ ordinary; cases ordinary
    | constructor valid typed =>
      intro children _
      exact .constructor valid (types (by simpa only [typingChildren] using children) typed)
    | member typed selected => intro children _; exact .member (children _ (by simp [typingChildren]) _ _ typed) selected
    | proxy admitted => intros; exact .proxy admitted
    | index base key =>
      intro children _
      exact .index (children _ (by simp [typingChildren]) _ _ base)
        (children _ (by simp [typingChildren]) _ _ key)


include edited avoids unique in
private theorem products {id : ExpressionId} (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionProducts.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | literal found atomic =>
    refine ⟨.literal ((expression_lookup edited avoids reached).symm.trans found) atomic, step edited avoids unique reached found ?_ ?_⟩
    · exact atomic_free atomic
    · simp [atomic_children atomic]
  | read found form =>
    refine ⟨.read ((expression_lookup edited avoids reached).symm.trans found) form, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · simp [form, typingChildren]
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem primitives {id : ExpressionId} (syntaxTree : CompatibleExpressionPrimitives.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionPrimitives.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | product child =>
    obtain ⟨certified, typed⟩ := products edited avoids unique child reached
    exact ⟨.product certified, typed⟩
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem conditionals {id : ExpressionId} (syntaxTree : CompatibleExpressionConditionals.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConditionals.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | primitive child =>
    obtain ⟨certified, typed⟩ := primitives edited avoids unique child reached
    exact ⟨.primitive certified, typed⟩
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem constructors {id : ExpressionId} (syntaxTree : CompatibleExpressionConstructors.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConstructors.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := conditionals edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2

include edited avoids unique in
private theorem members {id : ExpressionId} (syntaxTree : CompatibleExpressionMembers.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionMembers.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := constructors edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed

include edited avoids unique in
private theorem recursive {id : ExpressionId} (syntaxTree : CompatibleExpressionRecursive.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionRecursive.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := members edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed

include edited avoids unique in
private theorem general {id : ExpressionId} (syntaxTree : CompatibleExpressionGeneral.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionGeneral.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := recursive edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | proxy found form =>
    refine ⟨.proxy ((expression_lookup edited avoids reached).symm.trans found) form, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · simp [form, typingChildren]
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @index id node base key keyNode found form keyFound first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression key) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.index ((expression_lookup edited avoids reached).symm.trans found) form ((expression_lookup edited avoids secondReached).symm.trans keyFound) firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem builtins {id : ExpressionId} (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := general edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | proxy found form =>
    refine ⟨.proxy ((expression_lookup edited avoids reached).symm.trans found) form, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · simp [form, typingChildren]
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @index id node base key keyNode found form keyFound first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression key) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.index ((expression_lookup edited avoids reached).symm.trans found) form ((expression_lookup edited avoids secondReached).symm.trans keyFound) firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @builtin id node callee arguments function found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.builtin ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2

include edited avoids unique in
/-- The complete ordinary builtin syntax is transported only on reached nodes. -/
theorem expression_syntax {id : ExpressionId}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Syntax view id :=
  (builtins edited avoids unique syntaxTree reached).1

include edited avoids unique in
/-- Full independent typing retains the actual raw type, requirements and
coercions, including the reached builtin callee's declaration metadata. -/
theorem expression_typing {id : ExpressionId} {context : Context} {type : TypeSystem.Ty}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (reached : Reaches source roots (.expression id))
    (typed : ExpressionHasType source context id type) :
    ExpressionHasType view context id type :=
  (builtins edited avoids unique syntaxTree reached).2 context type typed

include edited in
private theorem reversed : LocalView view source changed :=
  ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩

include edited avoids unique in
/-- An accepted view's independent syntax recovers canonical source syntax.
Freshness and uniqueness are stated on the canonical source. -/
theorem expression_syntax_original {id : ExpressionId}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax view id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Syntax source id :=
  expression_syntax (reversed edited) (avoids.view edited.metadata) (edited.metadata.unique unique)
    syntaxTree (reached.metadata edited.metadata)

include edited avoids unique in
/-- The actual view's independent expression typing also recovers canonical
source typing; canonical compiler acceptance is not an assumption. -/
theorem expression_typing_original {id : ExpressionId} {context : Context} {type : TypeSystem.Ty}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax view id)
    (reached : Reaches source roots (.expression id))
    (typed : ExpressionHasType view context id type) :
    ExpressionHasType source context id type :=
  expression_typing (reversed edited) (avoids.view edited.metadata) (edited.metadata.unique unique)
    syntaxTree (reached.metadata edited.metadata) typed

include edited avoids unique in
/-- Lexical syntax transports the same reached expression certificates.
Independent expression typing follows the full source typing judgments. -/
theorem lexical_syntax_with {before after : ExpressionId → Prop}
    (expressions : ∀ id, Reaches source roots (.expression id) → before id → after id)
    {context : Context} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty}
    (syntaxTree : GenericLexicalStatements.Syntax source before context mode statements expected)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    GenericLexicalStatements.Syntax view after context mode statements expected := by
  induction syntaxTree with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form sourceType =>
    exact .returnUnit rest (edited.metadata.symm.statement found) form sourceType
  | @returnValue context mode id node expression expressionNode expected rest found form sourceType expressionFound valueType typed value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have certified := expressions _ child value
    exact .returnValue rest (edited.metadata.symm.statement found) form sourceType
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType (CallableLambdaViewStaticTyping.expression edited avoids unique typed child) certified
  | @tail context id node expression expressionNode expected found form sourceType expressionFound valueType typed value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have certified := expressions _ child value
    exact .tail (edited.metadata.symm.statement found) form sourceType
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType (CallableLambdaViewStaticTyping.expression edited avoids unique typed child) certified
  | @uninitialized context nextContext mode id node binder rest expected found form declaration mono extended ordinary remaining ih =>
    exact .uninitialized (edited.metadata.symm.statement found) form
      ((rootBinder edited.metadata binder.id).symm.trans declaration) mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType initializerTyped initializerSyntax remaining ih =>
    have child : Reaches source roots (.expression initializer) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have certified := expressions _ child initializerSyntax
    exact .initialized (edited.metadata.symm.statement found) form
      ((rootBinder edited.metadata binder.id).symm.trans declaration) mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (CallableLambdaViewStaticTyping.expression edited avoids unique initializerTyped child) certified
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed value remaining ih =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have certified := expressions _ child value
    exact .discard (edited.metadata.symm.statement found) form notTail sourceType
      ((expression_lookup edited avoids child).symm.trans expressionFound) (CallableLambdaViewStaticTyping.expression edited avoids unique typed child) certified
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    exact .block (edited.metadata.symm.statement found) form sourceType
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have certified := expressions _ child conditionSyntax
    exact .ifThen (edited.metadata.symm.statement found) form sourceType
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType (CallableLambdaViewStaticTyping.expression edited avoids unique typed child) certified
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))

  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    exact .terminalBlock (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form sourceType
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (stops.transport (statement_identity edited.metadata))
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have certified := expressions _ child conditionSyntax
    exact .terminalIf (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form sourceType
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType (CallableLambdaViewStaticTyping.expression edited avoids unique typed child) certified
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (thenStops.transport (statement_identity edited.metadata)) (elseStops.transport (statement_identity edited.metadata))

include edited avoids unique in
/-- The same reached static syntax transports back to the canonical source. -/
theorem lexical_syntax_original_with {before after : ExpressionId → Prop}
    (expressions : ∀ id, Reaches source roots (.expression id) → before id → after id)
    {context : Context} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty}
    (syntaxTree : GenericLexicalStatements.Syntax view before context mode statements expected)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    GenericLexicalStatements.Syntax source after context mode statements expected :=
  lexical_syntax_with (reversed edited) (avoids.view edited.metadata) (edited.metadata.unique unique)
    (fun id child childSyntax => expressions id (child.metadata edited.metadata.symm) childSyntax)
    syntaxTree (fun id member => (reached id member).metadata edited.metadata)

include edited avoids unique in
/-- Ordinary let/block/if syntax, with its independent expression typing,
transports at the actual lexical contexts. No body execution is stored here. -/
theorem lexical_syntax {context : Context} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty}
    (syntaxTree : BuiltinLexicalStatements.Syntax source context mode statements expected)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    BuiltinLexicalStatements.Syntax view context mode statements expected :=
  lexical_syntax_with edited avoids unique
    (fun _ child childSyntax => expression_syntax edited avoids unique childSyntax child) syntaxTree reached

include edited avoids unique in
theorem lexical_syntax_original {context : Context} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty}
    (syntaxTree : BuiltinLexicalStatements.Syntax view context mode statements expected)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    BuiltinLexicalStatements.Syntax source context mode statements expected :=
  lexical_syntax_original_with edited avoids unique
    (fun _ child childSyntax => expression_syntax_original edited avoids unique childSyntax child) syntaxTree reached

/-- Every statement in the actual body is its own reachability root. -/
theorem body_syntax {source view : TypedSource} {changed : List ExpressionId}
    {context : Context} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    (syntaxTree : BuiltinLexicalStatements.Syntax source context mode statements expected) :
    BuiltinLexicalStatements.Syntax view context mode statements expected :=
  lexical_syntax edited avoids unique syntaxTree (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))

/-- Canonical lexical syntax is recovered from view syntax without assuming
whole StatementsHaveType transport or canonical compiler success. -/
theorem body_syntax_original {source view : TypedSource} {changed : List ExpressionId}
    {context : Context} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    (syntaxTree : BuiltinLexicalStatements.Syntax view context mode statements expected) :
    BuiltinLexicalStatements.Syntax source context mode statements expected :=
  lexical_syntax_original edited avoids unique syntaxTree (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPreparedStaticTransport
/-! Static target constructor algebras retain each exact mapped Tree. They
carry no execution law and perform no traversal. The shared view transport
supplies every genuine constructor field and child packet once. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPreparedStaticTransport
open Core Frontend SourceInference
open GenericImperativeMatch GenericImperativeMatch.Structural

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

namespace Header
open GenericForHeader
variable {type : Ty} {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}

abbrev PacketMotive := ∀ {context scope items code},
  GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
    type continuation context scope items code → Prop

structure PacketAlgebra
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload) (P : PacketMotive (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation)) : Prop where
  nil : ∀ {context scope code}
      {next : continuation context scope code}
      , P (.nil next)
  uninitialized : ∀ {context nextContext scope binder rest body payload}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (TypedLexicalWhile.absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (TypedLexicalWhile.absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body}
      (_remainingErrors : P remaining)
      , P (.uninitialized monomorphic extended ordinary projected allocation annotation same remaining)
  initialized : ∀ {context nextContext scope binder initializer initializerNode lowered body rest}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (TypedLexicalWhile.initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (TypedLexicalWhile.initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body}
      (_remainingErrors : P remaining)
      , P (.initialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  discard : ∀ {context scope expression expressionNode rest lowered body}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (_remainingErrors : P remaining)
      , P (.discard found value remaining)
  assign : ∀ {context scope assignment operator rhs rest body}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (_remainingErrors : P remaining)
      (_headErrors : AP head)
      , P (.assign head remaining)
  bitNot : ∀ {context scope assignment rest body}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (_remainingErrors : P remaining)
      (_headErrors : UP head)
      , P (.bitNot head remaining)

theorem legacy_algebra {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    PacketAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation)
      (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
      (fun tree => tree.ErrorsFor diagnosticPolicy registry faults) := by
  refine {nil := ?_, uninitialized := ?_, initialized := ?_, discard := ?_, assign := ?_, bitNot := ?_}
  · intro context scope code next
    apply GenericForHeader.Tree.ErrorsFor.nil (context := context) (scope := scope) (code := code) (next := next)
    all_goals assumption
  · intro context nextContext scope binder rest body payload monomorphic extended ordinary projected allocation annotation same remaining remainingErrors
    apply GenericForHeader.Tree.ErrorsFor.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context nextContext scope binder initializer initializerNode lowered body rest monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors
    apply GenericForHeader.Tree.ErrorsFor.initialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context scope expression expressionNode rest lowered body found value remaining remainingErrors
    apply GenericForHeader.Tree.ErrorsFor.discard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (found := found) (value := value) (remaining := remaining)
    all_goals assumption
  · intro context scope assignment operator rhs rest body head remaining remainingErrors headErrors
    apply GenericForHeader.Tree.ErrorsFor.assign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope assignment rest body head remaining remainingErrors headErrors
    apply GenericForHeader.Tree.ErrorsFor.bitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (head := head) (remaining := remaining)
    all_goals assumption

theorem of_errors {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope items code}
    {tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code}
    (errors : Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      (values := values) (source := source) (certificates := certificates)
      (definitions := definitions) (administrative := administrative)
      (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults) context scope items code := by
  intro M algebra
  refine Tree.ErrorsFor.rec
    (motive := fun {context scope items code} _ _ => M context scope items code)
    ?_ ?_ ?_ ?_ ?_ ?_ errors
  · intro context scope code next
    exact algebra.nil next
  · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih
    exact algebra.uninitialized mono extended ordinary projected allocation annotation same ih
  · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining remainingErrors ih
    exact algebra.initialized mono extended ordinary found sourceType initial allocation annotation same ih
  · intro context scope expression expressionNode rest lowered body found value remaining remainingErrors ih
    exact algebra.discard found value ih
  · intro context scope assignment operator rhs rest body head remaining remainingErrors receipt ih
    exact algebra.assign head receipt ih
  · intro context scope assignment rest body head remaining remainingErrors receipt ih
    exact algebra.bitNot head receipt ih


variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- One selected post tree and its own plan survive each finite constructor. -/
def PreparedPacket {context scope items code}
    (tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
      type continuation context scope items code) : Prop :=
  ∃ plan : EmittedDiagnosticPlan.Plan factory,
    GenericForHeader.Coupled factory invalidProjection missingDefault tree plan ∧
    EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan

theorem prepared_algebra :
    PacketAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (certificates := certificates)
      (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation)
      (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
      (fun tree => PreparedPacket (factory := factory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree) := by
  refine {nil := ?_, uninitialized := ?_, initialized := ?_, discard := ?_, assign := ?_, bitNot := ?_}
  · intro context scope code next
    exact ⟨.pure, GenericForHeader.Coupled.nil (next := next), .pure⟩
  · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining child
    obtain ⟨plan, coupled, tokens⟩ := child
    exact ⟨plan, GenericForHeader.Coupled.uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) coupled, tokens⟩
  · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining child
    obtain ⟨plan, coupled, tokens⟩ := child
    exact ⟨plan, GenericForHeader.Coupled.initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) coupled, tokens⟩
  · intro context scope expression expressionNode rest lowered body found value remaining child
    obtain ⟨plan, coupled, tokens⟩ := child
    exact ⟨plan, GenericForHeader.Coupled.discard (found := found) (value := value) coupled, tokens⟩
  · intro context scope assignment operator rhs rest body head remaining child receipt
    obtain ⟨plan, coupled, tokens⟩ := child
    cases receipt with
    | intro site origin same sourceTyped rightTyped profile fuel prepared =>
      exact ⟨_, GenericForHeader.Coupled.assign (head := head) (remaining := remaining) coupled site origin same sourceTyped rightTyped profile fuel prepared,
        .pair tokens (.assignment head site origin same sourceTyped rightTyped profile)⟩
  · intro context scope assignment rest body head remaining child receipt
    obtain ⟨plan, coupled, tokens⟩ := child
    cases receipt with
    | intro writable bare profile site origin same =>
      exact ⟨_, GenericForHeader.Coupled.bitNot (head := head) (remaining := remaining) coupled writable bare profile,
        .pair tokens (.unary head writable bare profile site origin same)⟩

end Header

namespace Match
abbrev PacketMotive := ∀ {context scope position expected type code},
  GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope position expected type code → Prop

/-- The target payload is indexed by this exact supplied tree. -/
abbrev PacketAt (P : PacketMotive (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (expressionSyntax := expressionSyntax)) {context scope position expected type code}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code) : Prop := P tree

structure PacketAlgebra (AP : AssignmentPayload (values := values) (source := source) (certificates := certificates) (administrative := administrative) (definitions := definitions)) (UP : UnaryPayload) (HP : HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative)) (MP : MatchPayload)
    (P : PacketMotive (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (expressionSyntax := expressionSyntax)) : Prop where
  body : ∀ {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code},
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.body syntaxTree body)

  uninitialized : ∀ {context nextContext scope mode id node binder rest expected type body payload}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder none}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (TypedLexicalWhile.absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (TypedLexicalWhile.absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining)

  initialized : ∀ {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder (some initializer)}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (TypedLexicalWhile.initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (TypedLexicalWhile.initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)

  discard : ∀ {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.discard found form notTail expressionFound value remaining)

  block : ∀ {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_innerErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P inner)
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.block found form inner remaining)

  ifThen : ∀ {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_thenTreeErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P thenTree)
      (_elseTreeErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P elseTree)
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining)

  breaking : ∀ {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt},
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)

  continuing : ∀ {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt},
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)

  whileLoop : ∀ {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .whileLoop condition statements}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_loopBodyErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P loopBody)
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining)

  assign : ∀ {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining)
      (_headErrors : AP head),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.assign found form head remaining)


  bitNot : ∀ {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining)
      (_headErrors : UP head),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.bitNot found form head remaining)


  forLoop : ∀ {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (_initialErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P initial) (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.forLoop found form initial remaining)

  initializersDone : ∀ {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (_loopErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P loopBody) (_postErrors : HP postTree),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped)

  initializerUninitialized : ∀ {context nextContext scope binder rest body payload condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (TypedLexicalWhile.absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (TypedLexicalWhile.absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining)

  initializerInitialized : ∀ {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (TypedLexicalWhile.initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (TypedLexicalWhile.initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)

  initializerDiscard : ∀ {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.initializerDiscard found value remaining)

  initializerAssign : ∀ {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining)
      (_headErrors : AP head),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.initializerAssign head remaining)

  initializerBitNot : ∀ {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining)
      (_headErrors : UP head),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.initializerBitNot head remaining)

  matchWith : ∀ {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node} (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (_matchPayload : MP compilation context)
      (_childErrors : ∀ request member childContext valid, PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (children request member childContext valid))
      (_remainingErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P remaining),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children remaining)


  terminalBlock : ∀ {context scope mode id node statements rest expected type innerCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type innerCode}
      {stops : GenericLexicalStatements.Stopped source statements}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (_innerErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P inner),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.terminalBlock unique found form inner stops issued)

  terminalIf : ∀ {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .ifThen condition thenBody (some elseBody)}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false elseBody) expected type elseCode}
      {thenStops : GenericLexicalStatements.Stopped source thenBody}
      {elseStops : GenericLexicalStatements.Stopped source elseBody}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (_thenErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P thenTree)
      (_elseErrors : PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P elseTree),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P
        (.terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)


  terminalMatch : ∀ {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {stops : ReachableMatchContinuations.DefaultStopped source id resolution}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      (_matchPayload : MP compilation context)
      (_childErrors : ∀ request member childContext valid, PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (children request member childContext valid)),
      PacketAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := definitions) (administrative := administrative) P (.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children stops issued)


theorem legacy_algebra {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    PacketAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (expressionSyntax := expressionSyntax)
      (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
      (fun tree => tree.ErrorsFor diagnosticPolicy registry faults)
      (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ Tree.MatchContextFields compilation context)
      (fun tree => tree.CatalogSites diagnosticPolicy registry faults) := by
  refine {body := ?_, uninitialized := ?_, initialized := ?_, discard := ?_, block := ?_, ifThen := ?_, breaking := ?_, continuing := ?_, whileLoop := ?_, assign := ?_, bitNot := ?_, forLoop := ?_, initializersDone := ?_, initializerUninitialized := ?_, initializerInitialized := ?_, initializerDiscard := ?_, initializerAssign := ?_, initializerBitNot := ?_, matchWith := ?_, terminalBlock := ?_, terminalIf := ?_, terminalMatch := ?_}
  · intro context scope mode statements expected type code syntaxTree body
    apply GenericImperativeMatch.Tree.CatalogSites.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
    all_goals assumption
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining _innerErrors _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining _thenTreeErrors _elseTreeErrors _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node rest expected type found form
    apply GenericImperativeMatch.Tree.CatalogSites.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
    all_goals assumption
  · intro context scope mode id node rest expected type found form
    apply GenericImperativeMatch.Tree.CatalogSites.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
    all_goals assumption
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining _loopBodyErrors _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining _remainingErrors _headErrors
    apply GenericImperativeMatch.Tree.CatalogSites.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node assignment rest expected type body found form head remaining _remainingErrors _headErrors
    apply GenericImperativeMatch.Tree.CatalogSites.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining _initialErrors _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining)
    all_goals assumption
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped _loopErrors _postErrors
    apply GenericImperativeMatch.Tree.CatalogSites.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped)
    all_goals assumption
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining)
    all_goals assumption
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining _remainingErrors _headErrors
    apply GenericImperativeMatch.Tree.CatalogSites.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope assignment rest body condition post statements expected type head remaining _remainingErrors _headErrors
    apply GenericImperativeMatch.Tree.CatalogSites.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining _matchPayload _childErrors _remainingErrors
    apply GenericImperativeMatch.Tree.CatalogSites.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining)
    all_goals first | assumption | exact _matchPayload.1 | exact _matchPayload.2
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued _innerErrors
    apply GenericImperativeMatch.Tree.CatalogSites.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued)
    all_goals assumption
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued _thenErrors _elseErrors
    apply GenericImperativeMatch.Tree.CatalogSites.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued)
    all_goals assumption
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued _matchPayload _childErrors
    apply GenericImperativeMatch.Tree.CatalogSites.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued)
    all_goals first | assumption | exact _matchPayload.1 | exact _matchPayload.2

theorem structural_algebra
    (AP : AssignmentPayload (values := values) (source := source) (certificates := certificates) (administrative := administrative) (definitions := definitions))
    (UP : UnaryPayload)
    (HP : HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative))
    (MP : MatchPayload) :
    PacketAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (expressionSyntax := expressionSyntax) AP UP HP MP (fun {context scope position expected type code} _tree =>
      Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (expressionSyntax := expressionSyntax) AP UP HP MP context scope position expected type code) := by
  refine {body := ?_, uninitialized := ?_, initialized := ?_, discard := ?_, block := ?_, ifThen := ?_, breaking := ?_, continuing := ?_, whileLoop := ?_, assign := ?_, bitNot := ?_, forLoop := ?_, initializersDone := ?_, initializerUninitialized := ?_, initializerInitialized := ?_, initializerDiscard := ?_, initializerAssign := ?_, initializerBitNot := ?_, matchWith := ?_, terminalBlock := ?_, terminalIf := ?_, terminalMatch := ?_}
  · intro context scope mode statements expected type code syntaxTree body
    intro M algebra
    exact algebra.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining _remainingErrors
    intro M algebra
    exact algebra.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra)
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining _remainingErrors
    intro M algebra
    exact algebra.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining _remainingErrors
    intro M algebra
    exact algebra.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining _innerErrors _remainingErrors
    intro M algebra
    exact algebra.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining) (_innerErrors := _innerErrors M algebra) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining _thenTreeErrors _elseTreeErrors _remainingErrors
    intro M algebra
    exact algebra.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining) (_thenTreeErrors := _thenTreeErrors M algebra) (_elseTreeErrors := _elseTreeErrors M algebra) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope mode id node rest expected type found form
    intro M algebra
    exact algebra.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node rest expected type found form
    intro M algebra
    exact algebra.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining _loopBodyErrors _remainingErrors
    intro M algebra
    exact algebra.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining) (_loopBodyErrors := _loopBodyErrors M algebra) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining _remainingErrors _headErrors
    intro M algebra
    exact algebra.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra) (_headErrors := _headErrors)
  · intro context scope mode id node assignment rest expected type body found form head remaining _remainingErrors _headErrors
    intro M algebra
    exact algebra.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra) (_headErrors := _headErrors)
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining _initialErrors _remainingErrors
    intro M algebra
    exact algebra.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining) (_initialErrors := _initialErrors M algebra) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped _loopErrors _postErrors
    intro M algebra
    exact algebra.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped) (_loopErrors := _loopErrors M algebra) (_postErrors := _postErrors)
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining _remainingErrors
    intro M algebra
    exact algebra.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra)
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining _remainingErrors
    intro M algebra
    exact algebra.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining _remainingErrors
    intro M algebra
    exact algebra.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining _remainingErrors _headErrors
    intro M algebra
    exact algebra.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra) (_headErrors := _headErrors)
  · intro context scope assignment rest body condition post statements expected type head remaining _remainingErrors _headErrors
    intro M algebra
    exact algebra.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := _remainingErrors M algebra) (_headErrors := _headErrors)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining _matchPayload _childErrors _remainingErrors
    intro M algebra
    exact algebra.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining) (_matchPayload := _matchPayload) (_childErrors := fun request member childContext valid => _childErrors request member childContext valid M algebra) (_remainingErrors := _remainingErrors M algebra)
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued _innerErrors
    intro M algebra
    exact algebra.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued) (_innerErrors := _innerErrors M algebra)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued _thenErrors _elseErrors
    intro M algebra
    exact algebra.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (_thenErrors := _thenErrors M algebra) (_elseErrors := _elseErrors M algebra)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued _matchPayload _childErrors
    intro M algebra
    exact algebra.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued) (_matchPayload := _matchPayload) (_childErrors := fun request member childContext valid => _childErrors request member childContext valid M algebra)

end Match
end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPreparedStaticTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt
/-! A real compiler-view certificate and canonical body semantics share the
same finished Core code. Local edit reachability transports independent static
syntax and the concrete builtin Tree; canonical compiler acceptance is neither
required nor manufactured. Lambda formation and runtime history remain in the
caller's separate code and capture receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

structure Receipt (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source view : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (policy : SourceCoreLoops.Policy) (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  actual : BuiltinNamedBody.Certificate layouts owner active frame globals onError readFuel values view context solved reasonAt scope
    statements expected type policy fuel fellThrough escaped code
  canonical : BuiltinNamedBody.SemanticReceipt layouts owner active frame globals onError readFuel values source context solved reasonAt scope
    statements expected type fellThrough escaped code
  sameFlow : canonical.flow = actual.flow

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source view : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}

/-- The actual view acceptance is retained verbatim. Both canonical static
judgments are derived on the exact reached body, with no child meaning input. -/
def of_certificate {changed : List ExpressionId}
    (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    (certificate : BuiltinNamedBody.Certificate layouts owner active frame globals onError readFuel values view context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :
    Receipt layouts owner active frame globals onError readFuel values source view context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code :=
  ⟨certificate,
    BuiltinNamedBody.SemanticReceipt.of_tree certificate.projection
      (CallableLambdaViewSourceTyping.body_syntax_original edited avoids unique certificate.syntaxTree)
      certificate.emitted
      (CallableLambdaViewBuiltinBodyTree.original edited avoids certificate.tree), rfl⟩

/-- This is the accepted equation at the actual compiler view. -/
theorem Receipt.accepted
    (receipt : Receipt layouts owner active frame globals onError readFuel values source view context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :
    SourceCoreLoops.lowerStatementsWithPolicy policy fuel view scope statements
      type reasonAt fellThrough escaped = .ok code :=
  receipt.actual.accepted

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPlaceLowering
/-! Place lowering keeps the actual view expression callback while preserving
original binders and complete reached key nodes. No evaluation is transported. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPlaceLowering
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open CallableLambdaViewEdits CallableLambdaBodyReachability

theorem key_reference {projections : List PlaceProjection} {id : ExpressionId}
    (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    .expression id ∈ projections.flatMap PlaceProjection.references := by
  induction projections with
  | nil => cases member
  | cons projection rest ih =>
      cases projection with
      | member name index => exact ih member
      | index key =>
          rcases List.mem_cons.mp member with same | member
          · subst id
            simp [PlaceProjection.references]
          · exact List.mem_append_right _ (ih member)

private theorem routes {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view)
    {checked : Checked} {signatures : ProgramSignatures} {site : SourceCoreElaboration.ErrorSite}
    {root : Resolved.LocalId} {projections : List PlaceProjection}
    (keys : ∀ id ∈ DataPlaceKeyOrder.sourceKeys projections, source.lookupExpression? id = view.lookupExpression? id)
    (type : TypeSystem.Ty) :
    routeSteps checked signatures source site root type projections =
      routeSteps checked signatures view site root type projections := by
  induction projections generalizing type with
  | nil => rfl
  | cons projection rest ih =>
      cases projection with
      | member name index =>
          simp only [routeSteps, ih keys]
      | index key =>
          have first := keys key (List.mem_cons_self)
          have rest := fun id member => keys id (List.mem_cons_of_mem _ member)
          simp only [routeSteps, metadata.owner, first, ih rest]

theorem lower {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view)
    {values : SourceCoreCompatibleValues.Context} {signatures : ProgramSignatures} {expression : ExpressionLowerer}
    {fuel : Nat} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {output : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (keys : ∀ id ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections,
      source.lookupExpression? id = view.lookupExpression? id) :
    SourceCoreCompatibleDataPlaces.lower values signatures (fun fuel _ scope id reasonAt => expression fuel view scope id reasonAt)
        fuel source scope site assignment operator rhs output next reasonAt invalidProjection invalidOperand missing =
      SourceCoreCompatibleDataPlaces.lower values signatures expression fuel view scope site assignment operator rhs output next reasonAt
        invalidProjection invalidOperand missing := by
  have rootEq : SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root =
      SourceCoreCompatibleDataPlaces.rootBinder view assignment.target.root :=
    CallableLambdaBodyReachability.rootBinder metadata _
  have route : describe values signatures source site assignment = describe values signatures view site assignment := by
    simp only [describe, rootEq, routes metadata keys]
  simp only [SourceCoreCompatibleDataPlaces.lower, route]

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPlaceLowering
end
