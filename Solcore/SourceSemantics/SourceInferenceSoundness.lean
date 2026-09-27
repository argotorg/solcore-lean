import Solcore.Frontend.SourceInference.ProgramProperties
import Solcore.Frontend.SourceInference.RequirementProperties
import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.TraitResolutionSoundness

/-! Conditional bridge from executable finalization to declarative typing. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference

private theorem trait?_eq_some_facts
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {signature : ProgramTraitSignature}
    (found : signatures.trait? id = some signature) :
    signature ∈ signatures.traits ∧ signature.id = id := by
  have rawFound : signatures.traits.find?
      (fun candidate => decide (candidate.id = id)) = some signature := by
    simpa [ProgramSignatures.trait?] using found
  have accepted : decide (signature.id = id) = true :=
    List.find?_some
      (p := fun candidate : ProgramTraitSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private theorem list_eq_pair_of_length_eq_two
    {value : Type} {values : List value}
    (length_eq : values.length = 2) :
    ∃ first second, values = [first, second] := by
  cases values with
  | nil => simp at length_eq
  | cons first rest =>
      cases rest with
      | nil => simp at length_eq
      | cons second tail =>
          cases tail with
          | nil => exact ⟨first, second, rfl⟩
          | cons third tail => simp at length_eq

private theorem list_eq_singleton_of_length_eq_one
    {value : Type} {values : List value}
    (length_eq : values.length = 1) :
    ∃ item, values = [item] := by
  cases values with
  | nil => simp at length_eq
  | cons item rest =>
      cases rest with
      | nil => exact ⟨item, rfl⟩
      | cons second tail => simp at length_eq

private theorem list_perm_reverse {value : Type} (values : List value) :
    values.Perm values.reverse := by
  induction values with
  | nil => exact .nil
  | cons head tail induction =>
      rw [List.reverse_cons]
      exact (List.Perm.cons head induction).trans (by
        simpa only [List.singleton_append] using
          (List.perm_append_comm :
            ([head] ++ tail.reverse).Perm (tail.reverse ++ [head])))

/-- Finalized semantic schemes projected from the stable executable binder
stack.  The list order remains the executable lookup order; alignment with a
semantic context is therefore stated by permutation rather than equality. -/
def closedBinderLocals (substitution : TypeSystem.Substitution)
    (binders : List TypedBinder) :
    Resolved.LocalScope TypeSystem.Scheme :=
  binders.map fun binder =>
    (binder.id, (binder.applySubstitution substitution).scheme)

/-- Finalized qualified-requirement metadata paired with the same stable
binder identities as `closedBinderLocals`. -/
def closedBinderRequirements (substitution : TypeSystem.Substitution)
    (binders : List TypedBinder) :
    Resolved.LocalScope (List LocalSchemeRequirement) :=
  binders.map fun binder =>
    (binder.id, (binder.applySubstitution substitution).schemeRequirements)

/-- Stable executable binders and the two paired semantic local scopes carry
the same entries.  Initial parameters may be installed into the semantic
context in reverse order, so permutation plus unique identities is the exact
order-insensitive invariant. -/
structure LocalEnvironmentAligned
    (state : Frontend.SourceInference.State)
    (substitution : TypeSystem.Substitution)
    (context : SourceSemantics.Context) : Prop where
  ids_nodup : (state.localBinders.map fun binder => binder.id).Nodup
  locals_perm :
    (closedBinderLocals substitution state.localBinders).Perm context.locals
  requirements_perm :
    (closedBinderRequirements substitution state.localBinders).Perm
      context.localSchemeRequirements

namespace LocalEnvironmentAligned

/-- A monomorphic semantic binder extension over an empty lexical base
constructs the order-insensitive alignment for the corresponding closed
executable binders. -/
theorem ofMonoBindersExtend
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context final : SourceSemantics.Context}
    {owner : Resolved.DeclarationId} {types : List TypeSystem.Ty}
    (ids_nodup : (state.localBinders.map fun binder => binder.id).Nodup)
    (locals_empty : context.locals = [])
    (requirements_empty : context.localSchemeRequirements = [])
    (extension : MonoBindersExtend owner context
      (state.localBinders.map
        (TypedBinder.applySubstitution substitution)) types final) :
    LocalEnvironmentAligned state substitution final := by
  constructor
  · exact ids_nodup
  · rw [MonoBindersExtend.locals_eq extension, locals_empty,
      List.append_nil]
    simpa [closedBinderLocals, List.map_reverse, List.map_map,
      Function.comp_def, TypedBinder.applySubstitution] using
      list_perm_reverse (closedBinderLocals substitution state.localBinders)
  · rw [MonoBindersExtend.localSchemeRequirements_eq extension,
      requirements_empty, List.append_nil]
    simpa [closedBinderRequirements, List.map_reverse, List.map_map,
      Function.comp_def, TypedBinder.applySubstitution] using
      list_perm_reverse
        (closedBinderRequirements substitution state.localBinders)

/-- The stable input identities produced by `State.initial` discharge the
uniqueness premise of `ofMonoBindersExtend`. -/
theorem ofInitialMonoBindersExtend
    (owner : Resolved.DeclarationId) (locals : TypeSystem.Environment)
    (comptime : List Bool) (substitution : TypeSystem.Substitution)
    {context final : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (locals_empty : context.locals = [])
    (requirements_empty : context.localSchemeRequirements = [])
    (extension : MonoBindersExtend owner context
      ((Frontend.SourceInference.State.initial owner locals comptime
          ).localBinders.map
        (TypedBinder.applySubstitution substitution)) types final) :
    LocalEnvironmentAligned
      (Frontend.SourceInference.State.initial owner locals comptime)
      substitution final := by
  apply ofMonoBindersExtend
    (locals_empty := locals_empty)
    (requirements_empty := requirements_empty)
    (extension := extension)
  simpa only [← Frontend.SourceInference.State.initial_inputs_eq_localBinders]
    using MonoBindersExtend.initialInputIds_nodup owner locals comptime

/-- Replacing the legacy name-keyed local cache cannot affect the stable
binder alignment used by source semantics. -/
theorem withLocals
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (locals : TypeSystem.Environment) :
    LocalEnvironmentAligned (state.withLocals locals) substitution context := by
  constructor
  · exact aligned.ids_nodup
  · exact aligned.locals_perm
  · exact aligned.requirements_perm

/-- Allocating a fresh stable binder extends both executable and semantic
local scopes in lockstep.  The semantic entry is the closed view of the
newly allocated executable binder. -/
theorem allocateBinder
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    {binder : TypedBinder} {final : Frontend.SourceInference.State}
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final))
    (fresh : binder.id ∉ state.localBinders.map fun retained => retained.id) :
    LocalEnvironmentAligned final substitution
      (context.withLocal binder.id
        (binder.applySubstitution substitution).scheme
        (binder.applySubstitution substitution).schemeRequirements) := by
  have binder_eq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).1 = binder :=
    congrArg Prod.fst allocated
  have final_eq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).2 = final :=
    congrArg Prod.snd allocated
  subst binder
  subst final
  constructor
  · simpa [Frontend.SourceInference.State.allocateBinder] using
      (List.nodup_cons.mpr ⟨fresh, aligned.ids_nodup⟩)
  · simpa [closedBinderLocals,
      Frontend.SourceInference.State.allocateBinder,
      SourceSemantics.Context.withLocal] using
      aligned.locals_perm.cons
        ((state.allocateBinder name scheme span comptime
          schemeRequirements).1.id,
          ((state.allocateBinder name scheme span comptime
            schemeRequirements).1.applySubstitution substitution).scheme)
  · simpa [closedBinderRequirements,
      Frontend.SourceInference.State.allocateBinder,
      SourceSemantics.Context.withLocal] using
      aligned.requirements_perm.cons
        ((state.allocateBinder name scheme span comptime
          schemeRequirements).1.id,
          ((state.allocateBinder name scheme span comptime
            schemeRequirements).1.applySubstitution
              substitution).schemeRequirements)

/-- Executable first-match name lookup identifies a stable binder whose
closed scheme and qualified metadata are both available in the aligned
semantic context. -/
theorem lookup_of_lookupBinder?
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {name : String} {binder : TypedBinder}
    (aligned : LocalEnvironmentAligned state substitution context)
    (found : state.lookupBinder? name = some binder) :
    context.LocalLookup binder.id
        (binder.applySubstitution substitution).scheme ∧
      context.LocalSchemeRequirementsLookup binder.id
        (binder.applySubstitution substitution).schemeRequirements := by
  have rawFound : state.localBinders.find?
      (fun candidate => candidate.name == name) = some binder := by
    simpa [Frontend.SourceInference.State.lookupBinder?] using found
  have binderMember : binder ∈ state.localBinders :=
    List.mem_of_find?_eq_some rawFound
  have localMember :
      (binder.id, (binder.applySubstitution substitution).scheme) ∈
        closedBinderLocals substitution state.localBinders :=
    List.mem_map.mpr ⟨binder, binderMember, rfl⟩
  have requirementMember :
      (binder.id,
        (binder.applySubstitution substitution).schemeRequirements) ∈
        closedBinderRequirements substitution state.localBinders :=
    List.mem_map.mpr ⟨binder, binderMember, rfl⟩
  have closedLocalIdsNodup :
      ((closedBinderLocals substitution state.localBinders).map
        Prod.fst).Nodup := by
    simpa [closedBinderLocals, List.map_map, Function.comp_def,
      TypedBinder.applySubstitution] using aligned.ids_nodup
  have contextLocalIdsNodup :
      (context.locals.map Prod.fst).Nodup :=
    (aligned.locals_perm.map Prod.fst).nodup_iff.mp closedLocalIdsNodup
  have closedRequirementIdsNodup :
      ((closedBinderRequirements substitution state.localBinders).map
        Prod.fst).Nodup := by
    simpa [closedBinderRequirements, List.map_map, Function.comp_def,
      TypedBinder.applySubstitution] using aligned.ids_nodup
  have contextRequirementIdsNodup :
      (context.localSchemeRequirements.map Prod.fst).Nodup :=
    (aligned.requirements_perm.map Prod.fst).nodup_iff.mp
      closedRequirementIdsNodup
  constructor
  · exact Resolved.LocalScope.Lookup.of_mem_of_ids_nodup
      contextLocalIdsNodup (aligned.locals_perm.mem_iff.mp localMember)
  · exact Resolved.LocalScope.Lookup.of_mem_of_ids_nodup
      contextRequirementIdsNodup
        (aligned.requirements_perm.mem_iff.mp requirementMember)

/-- Forgetting executable names and semantic stable identities leaves the
same closed scheme collection on both sides of the alignment. -/
theorem localSchemes_perm
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context) :
    ((state.binderEnvironment.apply substitution).map Prod.snd).Perm
      (context.locals.map Prod.snd) := by
  have projected := aligned.locals_perm.map Prod.snd
  simpa [closedBinderLocals,
    Frontend.SourceInference.State.binderEnvironment,
    TypeSystem.Environment.apply, List.map_map, Function.comp_def,
    FlexibleSubstitution.applyTypedBinder_scheme] using projected

/-- The executable environment and aligned semantic local scope block
exactly the same flexible variables during local-value generalization. -/
theorem mem_local_freeVariables_iff
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (metavariable : TypeSystem.TypeVarId) :
    metavariable ∈
        (state.binderEnvironment.apply substitution).freeVariables ↔
      metavariable ∈ context.locals.flatMap
        (fun entry => entry.2.freeVariables) := by
  have schemesPerm := aligned.localSchemes_perm
  constructor
  · rw [TypeSystem.Environment.mem_freeVariables_iff]
    rintro ⟨entry, entryMember, variableMember⟩
    have sourceMember : entry.2 ∈
        (state.binderEnvironment.apply substitution).map Prod.snd :=
      List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    have targetMember : entry.2 ∈ context.locals.map Prod.snd :=
      schemesPerm.mem_iff.mp sourceMember
    rcases List.mem_map.mp targetMember with
      ⟨targetEntry, targetEntryMember, schemeEq⟩
    rw [List.mem_flatMap]
    exact ⟨targetEntry, targetEntryMember, by
      simpa [schemeEq] using variableMember⟩
  · rw [List.mem_flatMap]
    rintro ⟨entry, entryMember, variableMember⟩
    rw [TypeSystem.Environment.mem_freeVariables_iff]
    have targetMember : entry.2 ∈ context.locals.map Prod.snd :=
      List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    have sourceMember : entry.2 ∈
        (state.binderEnvironment.apply substitution).map Prod.snd :=
      schemesPerm.mem_iff.mpr targetMember
    rcases List.mem_map.mp sourceMember with
      ⟨sourceEntry, sourceEntryMember, schemeEq⟩
    exact ⟨sourceEntry, sourceEntryMember, by
      simpa [schemeEq] using variableMember⟩

end LocalEnvironmentAligned

/-- Any expression node retained by an inference state is declaratively
contained in every typed-source view of that state. -/
theorem toTypedSource_containsExpression_of_mem
    {state : Frontend.SourceInference.State} {node : ExpressionNode}
    (member : Node.expression node ∈ state.nodes)
    (roots : List NodeId := []) :
    ContainsExpression (state.toTypedSource roots) node.id node := by
  exact ⟨(by simpa [Frontend.SourceInference.State.toTypedSource] using member),
    rfl⟩

/-- Any statement node retained by an inference state is declaratively
contained in every typed-source view of that state. -/
theorem toTypedSource_containsStatement_of_mem
    {state : Frontend.SourceInference.State} {node : StatementNode}
    (member : Node.statement node ∈ state.nodes)
    (roots : List NodeId := []) :
    ContainsStatement (state.toTypedSource roots) node.id node := by
  exact ⟨(by simpa [Frontend.SourceInference.State.toTypedSource] using member),
    rfl⟩

/-- Recording an expression node immediately materializes declarative
expression containment. -/
theorem recordNode_containsExpression
    (state : Frontend.SourceInference.State) (node : ExpressionNode)
    (roots : List NodeId := []) :
    ContainsExpression
      ((state.recordNode (.expression node)).toTypedSource roots)
      node.id node := by
  apply toTypedSource_containsExpression_of_mem
  simp [Frontend.SourceInference.State.recordNode]

/-- Recording a statement node immediately materializes declarative
statement containment. -/
theorem recordNode_containsStatement
    (state : Frontend.SourceInference.State) (node : StatementNode)
    (roots : List NodeId := []) :
    ContainsStatement
      ((state.recordNode (.statement node)).toTypedSource roots)
      node.id node := by
  apply toTypedSource_containsStatement_of_mem
  simp [Frontend.SourceInference.State.recordNode]

/-- The expression-recording helper materializes its exact payload as a
declaratively contained expression node. -/
theorem recordExpression_containsExpression
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep)
    (state : Frontend.SourceInference.State) (roots : List NodeId := []) :
    ContainsExpression
      ((Detail.recordExpression source expression form requirements coercions
        state).2.toTypedSource roots)
      expression.id {
        id := expression.id
        span := source.span
        type := expression.type
        form
        requirements
        coercions
      } := by
  unfold Detail.recordExpression
  exact recordNode_containsExpression state _ roots

/-- Successful expected-type recording materializes the exact expression node
returned by the frontend, leaving only its fitted coercion path existential. -/
theorem recordExpressionWithExpected_success_containsExpression
    {context : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : TypeSystem.Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected context source id type form
      requirements expected state = .ok result)
    (roots : List NodeId := []) :
    ∃ coercions,
      ContainsExpression (result.2.toTypedSource roots) result.1.id {
        id := result.1.id
        span := source.span
        type := result.1.type
        form
        requirements := requirements ++
          Detail.coercionRequirements coercions
        coercions
      } := by
  obtain ⟨fitted, _, resultExpression, resultState⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  refine ⟨fitted.coercions, ?_⟩
  rw [resultState, resultExpression]
  exact recordNode_containsExpression fitted.state _ roots

/-- Successful executable graph validation establishes the complete initial
declarative occurrence-graph well-formedness layer. -/
theorem validateSourceGraph_success_occurrenceGraphWellFormed
    {source : TypedSource}
    (success : Detail.validateSourceGraph source = .ok ()) :
    OccurrenceGraphWellFormed source := by
  have unique :=
    Detail.validateSourceGraph_success_nodeOccurrencesUnique success
  have nodesOwned := Detail.validateSourceGraph_success_nodesOwned success
  have rootsExist := Detail.validateSourceGraph_success_rootsExist success
  have childEdges :=
    Detail.validateSourceGraph_success_childEdgesExist success
  refine {
    nodeOccurrencesUnique := by
      simpa [NodeOccurrencesUnique, nodeOccurrenceIds] using unique
    nodesOwned := by
      simpa [NodesOwned, OccurrenceOwnedBy] using nodesOwned
    rootsOwned := rootsOwned_of_nodesOwned_of_rootsExist
      (by simpa [NodesOwned, OccurrenceOwnedBy] using nodesOwned)
      (by simpa [RootsExist, nodeIds] using rootsExist)
    rootsExist := by
      simpa [RootsExist, nodeIds] using rootsExist
    childEdgesExist := by
      simpa [ChildEdgesExist, nodeChildIds, nodeIds] using childEdges
  }

/-- Executable local-identity validation establishes the declarative global
binder ownership invariant over the same canonical source inventory. -/
theorem validateSourceLocalIdentities_success_localIdentityOwnership
    {source : TypedSource}
    (success : Detail.validateSourceLocalIdentities source = .ok ()) :
    LocalIdentityOwnership source := by
  constructor
  · simpa using
      (Detail.validateSourceLocalIdentities_success_unique success)
  · intro id member
    exact Detail.validateSourceLocalIdentities_success_owned success id
      (by simpa using member)

private theorem lookupNodeId?_sound
    {source : TypedSource} {id : NodeId} {node : Node}
    (found : source.lookupNodeId? id = some node) :
    ContainsNode source id node := by
  have rawFound :
      source.nodes.find? (fun candidate => decide (candidate.id = id)) =
        some node := by
    simpa [TypedSource.lookupNodeId?] using found
  have member : node ∈ source.nodes :=
    List.mem_of_find?_eq_some rawFound
  have accepted : decide (node.id = id) = true :=
    List.find?_some
      (p := fun candidate : Node => decide (candidate.id = id)) rawFound
  exact ⟨member, of_decide_eq_true accepted⟩

/-- Every identity returned by the bounded root worklist is declaratively
reachable, provided its pending and already-collected inputs are reachable. -/
private theorem collectReachableNodeIdsFuel_sound
    {source : TypedSource} {fuel : Nat}
    {pending visited : List NodeId}
    (pendingReachable :
      ∀ id, id ∈ pending → Reachable source id)
    (visitedReachable :
      ∀ id, id ∈ visited → Reachable source id) :
    ∀ id,
      id ∈ Detail.collectReachableNodeIdsFuel source fuel pending visited →
        Reachable source id := by
  induction fuel generalizing pending visited with
  | zero =>
      simpa [Detail.collectReachableNodeIdsFuel] using visitedReachable
  | succ fuel induction =>
      cases pending with
      | nil =>
          simpa [Detail.collectReachableNodeIdsFuel] using visitedReachable
      | cons head tail =>
          cases alreadyVisited : Detail.nodeIdMember visited head with
          | true =>
              simp only [Detail.collectReachableNodeIdsFuel, alreadyVisited]
              apply induction
              · intro id member
                exact pendingReachable id (by simp [member])
              · exact visitedReachable
          | false =>
              cases found : source.lookupNodeId? head with
              | none =>
                  simp only [Detail.collectReachableNodeIdsFuel,
                    alreadyVisited, found]
                  apply induction
                  · intro id member
                    exact pendingReachable id (by simp [member])
                  · exact visitedReachable
              | some node =>
                  simp only [Detail.collectReachableNodeIdsFuel,
                    alreadyVisited, found]
                  have headReachable : Reachable source head :=
                    pendingReachable head (by simp)
                  have contains : ContainsNode source head node :=
                    lookupNodeId?_sound found
                  apply induction
                  · intro id member
                    rcases List.mem_append.mp member with childMember | tailMember
                    · exact .child headReachable
                        ⟨node, contains, childMember⟩
                    · exact pendingReachable id (by simp [tailMember])
                  · intro id member
                    rcases List.mem_cons.mp member with rfl | visitedMember
                    · exact headReachable
                    · exact visitedReachable id visitedMember

/-- Every identity collected by the public root worklist is reachable from a
declaration root in the declarative occurrence graph. -/
theorem sourceReachableNodeIds_sound
    (source : TypedSource) :
    ∀ id, id ∈ Detail.sourceReachableNodeIds source →
      Reachable source id := by
  unfold Detail.sourceReachableNodeIds
  apply collectReachableNodeIdsFuel_sound
  · intro id member
    exact .root member
  · simp

private theorem reachableFromSingletonRoot_inReflexiveSubtree
    {source : TypedSource} {root id : NodeId}
    (reachable : Reachable { source with roots := [root] } id) :
    InReflexiveSubtree source root id := by
  induction reachable with
  | @root found member =>
      exact Or.inl (by simpa using member)
  | @child parent child parentReachable edge induction =>
      have sourceEdge : DirectChild source parent child := by
        simpa [DirectChild, ContainsNode] using edge
      rcases induction with parentEq | parentPath
      · subst parent
        exact Or.inr (.direct sourceEdge)
      · exact Or.inr (Descends.trans parentPath (.direct sourceEdge))

/-- Every identity returned by the arbitrary-root executable worklist lies in
the declarative reflexive subtree rooted at that exact occurrence. -/
theorem sourceSubtreeNodeIds_sound
    (source : TypedSource) (root : NodeId) :
    ∀ id, id ∈ Detail.sourceSubtreeNodeIds source root →
      InReflexiveSubtree source root id := by
  intro id member
  apply reachableFromSingletonRoot_inReflexiveSubtree
  exact sourceReachableNodeIds_sound { source with roots := [root] } id (by
    simpa [Detail.sourceSubtreeNodeIds] using member)

/-- The executable template-scope validator and raw-ledger identity
uniqueness construct the exact declarative scoped-row witness for any source
template row. -/
theorem validateSourceTemplateScopes_success_rowScoped
    {source : TypedSource} {state : Frontend.SourceInference.State}
    (scopeSuccess : Detail.validateSourceTemplateScopes source state = .ok ())
    (ledgerUnique :
      (state.requirements.map fun requirement => requirement.id).Nodup)
    {requirement : Requirement}
    (requirementMember : requirement ∈ state.requirements)
    (templateMember :
      requirement.id ∈ sourceLocalSchemeTemplateIds source) :
    LocalSchemeTemplateRowScoped source {
      id := requirement.id
      predicate := Detail.applyPredicate state requirement.predicate
      evidence := .assumption
        (Detail.applyPredicate state requirement.predicate)
    } := by
  have executableTemplateMember :
      requirement.id ∈ source.localSchemeTemplateIds := by
    simpa using templateMember
  rw [typedSourceLocalSchemeTemplateIds_eq_sites] at executableTemplateMember
  rcases List.mem_map.mp executableTemplateMember with
    ⟨site, siteMember, siteIdEq⟩
  obtain ⟨selected, primary, selectedMember, selectedId,
      predicateEq, primaryMember, primaryId, primaryScoped⟩ :=
    Detail.validateSourceTemplateScopes_success scopeSuccess site siteMember
  have selectedEq : selected = requirement :=
    StructuralSubstitution.eq_of_mem_of_mapped_nodup ledgerUnique
      selectedMember requirementMember (selectedId.trans siteIdEq)
  subst selected
  have contains : ContainsLocalSchemeTemplate source site := by
    unfold ContainsLocalSchemeTemplate
    rw [← typedSourceLocalSchemeTemplateSites_eq_carrier]
    exact siteMember
  have primaryRequirementEq : primary.requirement = requirement.id :=
    primaryId.trans siteIdEq
  have occurs : PrimaryRequirementOccursAt source primary.occurrence
      requirement.id := by
    unfold PrimaryRequirementOccursAt
    rw [← typedSourcePrimaryRequirementSites_eq_carrier]
    cases primary with
    | mk occurrence primaryRequirement =>
        simp only at primaryRequirementEq ⊢
        subst primaryRequirement
        exact primaryMember
  exact .intro site contains siteIdEq.symm predicateEq
    (congrArg PredicateEvidence.assumption predicateEq)
    primary.occurrence occurs
    ⟨contains, sourceSubtreeNodeIds_sound source site.initializer
      primary.occurrence primaryScoped⟩

/-- Successful executable graph validation proves that every retained node is
reachable from one of the exact declaration roots. -/
theorem validateSourceGraph_success_allNodesReachable
    {source : TypedSource}
    (success : Detail.validateSourceGraph source = .ok ()) :
    AllNodesReachable source := by
  intro node member
  exact sourceReachableNodeIds_sound source node.id
    (Detail.validateSourceGraph_success_allNodesReached success node member)

/-- Successful executable validation establishes full rooted-forest closure,
including unique parents, total reachability, and acyclicity. -/
theorem validateSourceGraph_success_occurrenceGraphClosed
    {source : TypedSource}
    (success : Detail.validateSourceGraph source = .ok ()) :
    OccurrenceGraphClosed source :=
  OccurrenceGraphClosed.of_wellFormed_incomingUnique_reachable
    (validateSourceGraph_success_occurrenceGraphWellFormed success)
    (Detail.validateSourceGraph_success_incomingNodeIds_nodup success)
    (validateSourceGraph_success_allNodesReachable success)

/-- Successful finalization emits a source whose occurrence table, roots, and
direct child edges satisfy the declarative graph invariant. -/
theorem finalize_occurrenceGraphWellFormed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    OccurrenceGraphWellFormed result.typedSource := by
  have inputWellFormed :
      OccurrenceGraphWellFormed (state.toTypedSource roots) :=
    validateSourceGraph_success_occurrenceGraphWellFormed
      (Detail.finalize_validateSourceGraph success)
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.OccurrenceGraphWellFormed.applySubstitution
    result.substitution inputWellFormed

/-- Successful finalization emits a fully closed rooted occurrence forest. -/
theorem finalize_occurrenceGraphClosed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    OccurrenceGraphClosed result.typedSource := by
  have inputClosed : OccurrenceGraphClosed (state.toTypedSource roots) :=
    validateSourceGraph_success_occurrenceGraphClosed
      (Detail.finalize_validateSourceGraph success)
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.OccurrenceGraphClosed.applySubstitution
    result.substitution inputClosed

/-- Every successfully checked function body retains a closed occurrence
forest, including exact ownership, incoming-edge uniqueness and reachability. -/
theorem checkFunctionBody_success_occurrenceGraphClosed
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    OccurrenceGraphClosed checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_occurrenceGraphClosed finalizeSuccess

/-- Successful finalization validates every local definition before closing
types, and final substitution preserves those stable identities exactly. -/
theorem finalize_localIdentityOwnership
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    LocalIdentityOwnership result.typedSource := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.LocalIdentityOwnership.applySubstitution
    result.substitution
    (validateSourceLocalIdentities_success_localIdentityOwnership
      (Detail.finalize_validateSourceLocalIdentities success))

/-- Every successfully checked function body carries globally unique stable
locals owned by that function declaration. -/
theorem checkFunctionBody_success_localIdentityOwnership
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    LocalIdentityOwnership checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_localIdentityOwnership finalizeSuccess

/-- Every expression entry root supplied to successful finalization has a
concrete expression node in the emitted source. -/
theorem finalize_expression_root_exists
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    {id : ExpressionId} (member : NodeId.expression id ∈ roots) :
    ∃ node, ContainsExpression result.typedSource id node := by
  apply (finalize_occurrenceGraphWellFormed success).expression_root_exists
  rw [Detail.finalize_typedSource success]
  simpa [Frontend.SourceInference.State.toTypedSource] using member

/-- Every statement entry root supplied to successful finalization has a
concrete statement node in the emitted source. -/
theorem finalize_statement_root_exists
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    {id : StatementId} (member : NodeId.statement id ∈ roots) :
    ∃ node, ContainsStatement result.typedSource id node := by
  apply (finalize_occurrenceGraphWellFormed success).statement_root_exists
  rw [Detail.finalize_typedSource success]
  simpa [Frontend.SourceInference.State.toTypedSource] using member

/-- Finalization transports every retained expression node into the emitted
typed source under exactly the substitution returned to callers. -/
theorem finalize_containsExpression_of_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    {node : ExpressionNode}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (member : Node.expression node ∈ state.nodes) :
    ContainsExpression result.typedSource node.id
      (node.applySubstitution result.substitution) := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.ContainsExpression.applySubstitution
    result.substitution
    (toTypedSource_containsExpression_of_mem member roots)

/-- Finalization transports every retained statement node into the emitted
typed source under exactly the substitution returned to callers. -/
theorem finalize_containsStatement_of_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    {node : StatementNode}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (member : Node.statement node ∈ state.nodes) :
    ContainsStatement result.typedSource node.id
      (node.applySubstitution result.substitution) := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.ContainsStatement.applySubstitution
    result.substitution
    (toTypedSource_containsStatement_of_mem member roots)

/-- The executable binary dispatch table agrees exactly with the declarative
trait dispatch relation on every trait-backed spelling. -/
theorem binaryOperatorDispatch_traitMethod
    {operator : Syntax.BinaryOp} {traitName methodName : String}
    (dispatch : Detail.binaryOperatorDispatch operator =
      .traitMethod traitName methodName) :
    BinaryTraitDispatch operator traitName methodName := by
  cases operator <;>
    simp [Detail.binaryOperatorDispatch] at dispatch
  all_goals rcases dispatch with ⟨rfl, rfl⟩
  all_goals constructor

/-- The executable unary dispatch table agrees exactly with the declarative
trait dispatch relation on its trait-backed spelling. -/
theorem unaryOperatorDispatch_traitMethod
    {operator : Syntax.UnaryOp} {traitName methodName : String}
    (dispatch : Detail.unaryOperatorDispatch operator =
      .traitMethod traitName methodName) :
    UnaryTraitDispatch operator traitName methodName := by
  cases operator <;>
    simp [Detail.unaryOperatorDispatch] at dispatch
  rcases dispatch with ⟨rfl, rfl⟩
  constructor

/-- Exact successful branch retained by unary-operator inference before final
substitution.  The only non-semantic primitive case is an open integer-literal
target deliberately deferred to finalization. -/
inductive UnaryOperatorInferenceCase
    (inferenceContext : Frontend.SourceInference.Context)
    (semanticContext : SourceSemantics.Context)
    (initial : Frontend.SourceInference.State)
    (operator : Syntax.UnaryOp) (operandType : TypeSystem.Ty)
    (integerLiterals : List IntegerLiteralOrigin)
    (result : Detail.OperatorInferenceResult) : Prop where
  | primitive
      (typing : UnaryOperatorHasType semanticContext operator
        (result.state.resolve operandType) result.type result.requirements) :
      UnaryOperatorInferenceCase inferenceContext semanticContext initial
        operator operandType integerLiterals result
  | deferredBitNot
      (operator_eq : operator = .bitNot)
      (requirements_eq : result.requirements = [])
      (type_eq : result.type = result.state.resolve operandType)
      (deferred : Detail.isDeferredBuiltinOperatorTarget result.state
        (Detail.isOpenIntegerLiteralTarget initial integerLiterals operandType)
        .word (result.state.resolve operandType) = true) :
      UnaryOperatorInferenceCase inferenceContext semanticContext initial
        operator operandType integerLiterals result
  | trait
      {trait : Resolved.DeclarationId} {traitName methodName : String}
      {predicates : List ProgramPredicate}
      (dispatch : UnaryTraitDispatch operator traitName methodName)
      (selected : Detail.operatorTrait? inferenceContext traitName =
        .ok (some trait))
      (profile : Detail.operatorTraitPredicates inferenceContext trait
        methodName (result.state.resolve operandType)
        [result.state.resolve operandType] [result.type] = .ok predicates)
      (corresponds : RequirementPredicatesCorrespond result.state.requirements
        predicates result.requirements) :
      UnaryOperatorInferenceCase inferenceContext semanticContext initial
        operator operandType integerLiterals result

/-- Exact successful branch retained by binary-operator inference before final
substitution.  Direct builtins already carry declarative typing, trait calls retain
their selected profile and requirement correspondence, and the literal-only
fallback is isolated for final defaulting. -/
inductive BinaryOperatorInferenceCase
    (inferenceContext : Frontend.SourceInference.Context)
    (semanticContext : SourceSemantics.Context)
    (initial : Frontend.SourceInference.State)
    (operator : Syntax.BinaryOp) (left right : TypeSystem.Ty)
    (integerLiterals : List IntegerLiteralOrigin)
    (result : Detail.OperatorInferenceResult) : Prop where
  | primitive
      (typing : BinaryOperatorHasType semanticContext operator
        (result.state.resolve left) (result.state.resolve right)
        result.type result.requirements) :
      BinaryOperatorInferenceCase inferenceContext semanticContext initial
        operator left right integerLiterals result
  | literalFallback
      (requirements_eq : result.requirements = [])
      (operands_eq : result.state.resolve left = result.state.resolve right)
      (type_eq : result.type = if Detail.binaryResultIsBool operator
        then .bool else result.state.resolve left)
      (fallback :
        Detail.isDeferredBuiltinOperatorTarget result.state
            (Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
              Detail.isOpenIntegerLiteralTarget initial integerLiterals right)
            (Detail.binaryBuiltinType operator)
            (result.state.resolve left) = true ∨
          Detail.isStagedIntegerOperatorTarget result.state
            (Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
              Detail.isOpenIntegerLiteralTarget initial integerLiterals right)
            (Detail.binaryBuiltinType operator)
            (result.state.resolve left) = true) :
      BinaryOperatorInferenceCase inferenceContext semanticContext initial
        operator left right integerLiterals result
  | trait
      {trait : Resolved.DeclarationId} {traitName methodName : String}
      {predicates : List ProgramPredicate}
      (operands_eq : result.state.resolve left = result.state.resolve right)
      (dispatch : BinaryTraitDispatch operator traitName methodName)
      (selected : Detail.operatorTrait? inferenceContext traitName =
        .ok (some trait))
      (profile : Detail.operatorTraitPredicates inferenceContext trait
        methodName (result.state.resolve left)
        [result.state.resolve left, result.state.resolve left] [result.type] =
          .ok predicates)
      (corresponds : RequirementPredicatesCorrespond result.state.requirements
        predicates result.requirements) :
      BinaryOperatorInferenceCase inferenceContext semanticContext initial
        operator left right integerLiterals result

/-- The fixed builtin type and result table is a declarative binary typing
table for every operator spelling. -/
theorem binaryBuiltin_hasType
    (context : SourceSemantics.Context) (operator : Syntax.BinaryOp) :
    BinaryOperatorHasType context operator
      (Detail.binaryBuiltinType operator)
      (Detail.binaryBuiltinType operator)
      (if Detail.binaryResultIsBool operator then .bool
        else Detail.binaryBuiltinType operator) [] := by
  cases operator <;>
    simp [Detail.binaryBuiltinType, Detail.binaryResultIsBool]
  all_goals constructor
  all_goals constructor

/-- Every Word-backed binary builtin also has the staged integer typing used
while literal targets are being finalized. -/
theorem binaryInteger_hasType
    (context : SourceSemantics.Context) (operator : Syntax.BinaryOp)
    (word_builtin : Detail.binaryBuiltinType operator = TypeSystem.Ty.word) :
    BinaryOperatorHasType context operator .integer .integer
      (if Detail.binaryResultIsBool operator then .bool else .integer) [] := by
  cases operator <;>
    simp [Detail.binaryBuiltinType, Detail.binaryResultIsBool,
      TypeSystem.Ty.bool, TypeSystem.Ty.word] at word_builtin ⊢
  all_goals constructor
  all_goals constructor

/-- Requirement allocation leaves the inference substitution, and therefore
type resolution, unchanged. -/
@[simp] theorem addRequirementsWithIds_resolve
    (state : Frontend.SourceInference.State)
    (predicates : List ProgramPredicate) (type : TypeSystem.Ty) :
    (state.addRequirementsWithIds predicates).2.resolve type =
      state.resolve type := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [Frontend.SourceInference.State.addRequirementsWithIds]
      rw [induction]
      rfl

/-- Allocating a source-ordered predicate row records exactly the returned
requirement identities in the enlarged canonical ledger. -/
theorem addRequirementsWithIds_correspond
    (state : Frontend.SourceInference.State)
    (predicates : List ProgramPredicate) :
    RequirementPredicatesCorrespond
      (state.addRequirementsWithIds predicates).2.requirements predicates
      (state.addRequirementsWithIds predicates).1 := by
  induction predicates generalizing state with
  | nil => exact .nil
  | cons predicate rest induction =>
      simp only [Frontend.SourceInference.State.addRequirementsWithIds]
      apply RequirementPredicatesCorrespond.cons
      · have included :=
          Frontend.SourceInference.State.addRequirementsWithIds_requirements_subset
            (state.addRequirementWithId predicate).2 rest
        apply included
        simp [Frontend.SourceInference.State.addRequirementWithId]
      · exact induction (state.addRequirementWithId predicate).2

/-- Every successful unary-operator inference step is already a declarative
primitive or trait typing, except for the one open Word-literal target which
is intentionally left to final defaulting.  Solvedness is explicit because
the staged-integer test normalizes an already resolved operand once more. -/
theorem inferUnaryOperator_success_case
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {operator : Syntax.UnaryOp} {operandType : TypeSystem.Ty}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {initial : Frontend.SourceInference.State}
    {result : Detail.OperatorInferenceResult}
    (success : Detail.inferUnaryOperator inferenceContext operator operandType
      expected integerLiterals initial = .ok result)
    (result_solved : result.state.inference.Solved) :
    UnaryOperatorInferenceCase inferenceContext semanticContext initial
      operator operandType integerLiterals result := by
  have resolve_idempotent :
      result.state.resolve (result.state.resolve operandType) =
        result.state.resolve operandType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        result_solved.apply_idempotent operandType
  have logicalNot_beq :
      (Syntax.UnaryOp.logicalNot == Syntax.UnaryOp.logicalNot) = true := rfl
  have bitNot_beq :
      (Syntax.UnaryOp.bitNot == Syntax.UnaryOp.logicalNot) = false := rfl
  have bool_word_beq :
      (TypeSystem.Ty.bool == TypeSystem.Ty.word) = false := rfl
  have word_word_beq :
      (TypeSystem.Ty.word == TypeSystem.Ty.word) = true := rfl
  cases operator <;>
    unfold Detail.inferUnaryOperator at success <;>
    simp_all [bind, Except.bind] <;>
    repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all [Detail.unaryOperatorDispatch]
  all_goals try exact .primitive (by
    simp_all
    first | exact .logicalNot | exact .wordBitNot | exact .integerBitNot)
  all_goals try simp_all [Detail.isDeferredBuiltinOperatorTarget,
    Detail.isStagedIntegerOperatorTarget, bool_word_beq, word_word_beq]
  all_goals try grind [Detail.isDeferredBuiltinOperatorTarget,
    Detail.isStagedIntegerOperatorTarget, TypeSystem.Ty.bool,
    TypeSystem.Ty.word, TypeSystem.Ty.integer]
  all_goals try obtain ⟨rfl, rfl⟩ := ‹"BitNot" = _ ∧ "bnot" = _›
  all_goals subst_vars
  all_goals first
    | exact UnaryOperatorInferenceCase.trait
        (dispatch := UnaryTraitDispatch.bitNot)
        (selected := by assumption)
        (profile := by simpa using (by assumption))
        (corresponds := addRequirementsWithIds_correspond _ _)
    | skip
  all_goals
    rcases ‹_ ∨ _› with deferred | staged
    · exact UnaryOperatorInferenceCase.deferredBitNot rfl rfl rfl (by simp_all)
    · exact UnaryOperatorInferenceCase.primitive (by
        simp_all [Detail.isStagedIntegerOperatorTarget, TypeSystem.Ty.word]
        exact UnaryOperatorHasType.integerBitNot)

/-- The tail shared by all expected-type branches of binary inference.  This
is definitionally the suffix of `Detail.inferBinaryOperator`; naming it keeps
the successful branch inversion local and readable. -/
private def finishBinaryOperator
    (context : Frontend.SourceInference.Context) (operator : Syntax.BinaryOp)
    (left right : TypeSystem.Ty)
    (integerLiterals : List IntegerLiteralOrigin)
    (initial state : Frontend.SourceInference.State) :
    Except Frontend.SourceInference.Error Detail.OperatorInferenceResult := do
  let hasOpenLiteralOperand :=
    Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
      Detail.isOpenIntegerLiteralTarget initial integerLiterals right
  let operand := state.resolve left
  let builtin := Detail.binaryBuiltinType operator
  if operand = builtin then
    pure {
      type := if Detail.binaryResultIsBool operator then .bool else builtin
      requirements := []
      state
    }
  else
    match Detail.binaryOperatorDispatch operator with
    | .function name =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure {
            type := if Detail.binaryResultIsBool operator then .bool else operand
            requirements := []
            state
          }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName =>
        match ← Detail.operatorTrait? context traitName with
        | some trait =>
            let result := if Detail.binaryResultIsBool operator then .bool
              else operand
            let predicates ←
              Detail.operatorTraitPredicates context trait methodName operand
                [operand, operand] [result]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure { type := result, requirements, state }
        | none =>
            if Detail.isDeferredBuiltinOperatorTarget state
                  hasOpenLiteralOperand builtin operand ||
                Detail.isStagedIntegerOperatorTarget state
                  hasOpenLiteralOperand builtin operand then
              pure {
                type := if Detail.binaryResultIsBool operator then .bool
                  else operand
                requirements := []
                state
              }
            else
              throw (.operatorNotSupported traitName operand)

private theorem finishBinaryOperator_success_case
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {operator : Syntax.BinaryOp} {left right : TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {initial state : Frontend.SourceInference.State}
    {result : Detail.OperatorInferenceResult}
    (operands_eq : state.resolve left = state.resolve right)
    (success : finishBinaryOperator inferenceContext operator left right
      integerLiterals initial state = .ok result) :
    BinaryOperatorInferenceCase inferenceContext semanticContext initial
      operator left right integerLiterals result := by
  unfold finishBinaryOperator at success
  simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at success
  by_cases operand_builtin :
      state.resolve left = Detail.binaryBuiltinType operator
  · simp [operand_builtin] at success
    cases success
    exact .primitive (by
      rw [← operands_eq, operand_builtin]
      exact binaryBuiltin_hasType semanticContext operator)
  · cases dispatch_eq : Detail.binaryOperatorDispatch operator with
    | function name =>
        simp only [operand_builtin, ↓reduceIte, dispatch_eq] at success
        by_cases fallback :
            (Detail.isDeferredBuiltinOperatorTarget state
                  (Detail.isOpenIntegerLiteralTarget initial integerLiterals
                    left ||
                    Detail.isOpenIntegerLiteralTarget initial integerLiterals
                      right)
                  (Detail.binaryBuiltinType operator) (state.resolve left) ||
              Detail.isStagedIntegerOperatorTarget state
                  (Detail.isOpenIntegerLiteralTarget initial integerLiterals
                    left ||
                    Detail.isOpenIntegerLiteralTarget initial integerLiterals
                      right)
                  (Detail.binaryBuiltinType operator) (state.resolve left)) =
              true
        · simp [fallback] at success
          cases success
          exact .literalFallback rfl operands_eq rfl (by simpa using fallback)
        · simp [fallback] at success
    | traitMethod traitName methodName =>
        simp only [operand_builtin, ↓reduceIte, dispatch_eq] at success
        cases selected : Detail.operatorTrait? inferenceContext traitName with
        | error error => simp [selected] at success
        | ok selection =>
            cases selection with
            | none =>
                by_cases fallback :
                    (Detail.isDeferredBuiltinOperatorTarget state
                          (Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals left ||
                            Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals right)
                          (Detail.binaryBuiltinType operator)
                          (state.resolve left) ||
                      Detail.isStagedIntegerOperatorTarget state
                          (Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals left ||
                            Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals right)
                          (Detail.binaryBuiltinType operator)
                          (state.resolve left)) = true
                · simp [selected, fallback] at success
                  cases success
                  exact .literalFallback rfl operands_eq rfl
                    (by simpa using fallback)
                · simp [selected, fallback] at success
            | some trait =>
                cases profile : Detail.operatorTraitPredicates inferenceContext
                    trait methodName (state.resolve left)
                    [state.resolve left, state.resolve left]
                    [if Detail.binaryResultIsBool operator then .bool
                      else state.resolve left] with
                | error error => simp [selected, profile] at success
                | ok predicates =>
                    simp [selected, profile] at success
                    cases success
                    exact .trait
                      (operands_eq := by simpa using operands_eq)
                      (dispatch :=
                        binaryOperatorDispatch_traitMethod dispatch_eq)
                      (selected := selected)
                      (profile := by simpa using profile)
                      (corresponds :=
                        addRequirementsWithIds_correspond state predicates)

/-- Every successful binary-operator inference step is exactly a direct
builtin, a selected trait profile with its allocated evidence rows, or the
literal-only fallback deliberately left to final defaulting. -/
theorem inferBinaryOperator_success_case
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {operator : Syntax.BinaryOp} {left right : TypeSystem.Ty}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {initial : Frontend.SourceInference.State}
    {result : Detail.OperatorInferenceResult}
    (success : Detail.inferBinaryOperator inferenceContext operator left right
      expected integerLiterals initial = .ok result) :
    BinaryOperatorInferenceCase inferenceContext semanticContext initial
      operator left right integerLiterals result := by
  unfold Detail.inferBinaryOperator at success
  simp only [bind, Except.bind] at success
  cases first_unify : Detail.unify initial left right with
  | error error => simp [first_unify] at success
  | ok unified =>
      have unified_eq := Detail.unify_resolve_eq first_unify
      simp only [first_unify] at success
      cases expected with
      | none =>
          simp only [pure, Pure.pure, Except.pure]
            at success
          exact finishBinaryOperator_success_case unified_eq success
      | some expected =>
          simp only [pure, Pure.pure, Except.pure]
            at success
          split at success
          · exact finishBinaryOperator_success_case unified_eq success
          · cases second_unify : Detail.unify unified
                (unified.resolve left) expected with
            | error error => simp [second_unify] at success
            | ok prepared =>
                have prepared_eq :=
                  Detail.unify_preserves_resolve_eq unified_eq second_unify
                simp only [second_unify] at success
                exact finishBinaryOperator_success_case prepared_eq success

/-- A successfully loaded coercion-method profile and its successfully
instantiated predicate row supply the declarative `Coerce` profile used by
source typing.  The explicit name premise isolates the remaining
environment-to-signature catalog alignment obligation; independently assembled
inference contexts are not otherwise required to keep those names aligned. -/
theorem coercionMethodProfile?_some_instantiates
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {source target : TypeSystem.Ty}
    {methodPredicates : List ProgramPredicate}
    (signatures_eq :
      semanticContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (predicates_success :
      Detail.coercionMethodPredicates (some profile) source target =
        .ok methodPredicates) :
    CoercionProfileInstantiates semanticContext source target {
      trait := .declaration trait
      subject := source
      arguments := [target]
    } methodPredicates := by
  cases signature_lookup : inferenceContext.signatures.trait? trait with
  | none =>
      simp [signature_lookup] at trait_name
  | some signature =>
      have signature_name : signature.name = "Coerce" := by
        simpa [signature_lookup] using trait_name
      have signature_facts := trait?_eq_some_facts signature_lookup
      simp only [Detail.coercionMethodProfile?, signature_lookup, pure,
        Pure.pure, Except.pure, bind, Except.bind] at profile_success
      by_cases arity : signature.parameters.length = 2
      · rw [if_pos arity] at profile_success
        obtain ⟨fromParameter, toParameter, parameters_eq⟩ :=
          list_eq_pair_of_length_eq_two arity
        cases methods_eq : signature.methods.filter
            (fun candidate => candidate.name == "coerce") with
        | nil =>
            rw [methods_eq] at profile_success
            simp at profile_success
        | cons method rest =>
            cases rest with
            | nil =>
                rw [methods_eq] at profile_success
                simp only [Except.ok.injEq, Option.some.injEq] at profile_success
                subst profile
                by_cases parameter_types_eq :
                    method.parameterTypes.map
                        (TypeSystem.ParameterSubstitution.apply
                          [(fromParameter, source), (toParameter, target)]) =
                      [source]
                · by_cases return_types_eq :
                      method.returnTypes.map
                          (TypeSystem.ParameterSubstitution.apply
                            [(fromParameter, source), (toParameter, target)]) =
                        [target]
                  · have predicate_eq :
                        method.wherePredicates.map
                            (ProgramPredicate.applyParameters
                              [(fromParameter, source),
                                (toParameter, target)]) =
                          methodPredicates := by
                      simpa [Detail.coercionMethodPredicates, parameters_eq,
                        parameter_types_eq, return_types_eq] using
                          predicates_success
                    rw [← signature_facts.2, ← predicate_eq]
                    exact .intro
                      (by rw [signatures_eq]; exact signature_facts.1)
                      signature_name parameters_eq methods_eq
                      parameter_types_eq return_types_eq
                  · simp [Detail.coercionMethodPredicates, parameters_eq,
                      parameter_types_eq, return_types_eq, bind, Except.bind]
                      at predicates_success
                · simp [Detail.coercionMethodPredicates, parameters_eq,
                    parameter_types_eq, bind, Except.bind]
                    at predicates_success
            | cons second tail =>
                rw [methods_eq] at profile_success
                simp at profile_success
      · rw [if_neg arity] at profile_success
        simp at profile_success

/-- Successful operator-method profile validation supplies the declarative
profile used by unary and binary source typing.  The explicit trait-name
premise isolates the environment-to-signature alignment obligation in the
same way as the coercion-profile bridge above. -/
theorem operatorTraitPredicates_instantiates
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {operand : TypeSystem.Ty}
    {expectedParameters expectedReturns : List TypeSystem.Ty}
    {predicates : List ProgramPredicate}
    (signatures_eq :
      semanticContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (success : Detail.operatorTraitPredicates inferenceContext trait methodName
      operand expectedParameters expectedReturns = .ok predicates) :
    OperatorProfileInstantiates semanticContext traitName methodName operand
      expectedParameters expectedReturns predicates := by
  cases signature_lookup : inferenceContext.signatures.trait? trait with
  | none =>
      simp [signature_lookup] at trait_name
  | some signature =>
      have signature_name : signature.name = traitName := by
        simpa [signature_lookup] using trait_name
      have signature_facts := trait?_eq_some_facts signature_lookup
      simp only [Detail.operatorTraitPredicates,
        Detail.exactOperatorTraitMethod, signature_lookup, pure, Pure.pure,
        Except.pure, bind, Except.bind] at success
      cases methods_eq : signature.methods.filter
          (fun candidate => candidate.name == methodName) with
      | nil =>
          rw [methods_eq] at success
          simp at success
      | cons method rest =>
          cases rest with
          | nil =>
              rw [methods_eq] at success
              simp only at success
              by_cases arity : signature.parameters.length = 1
              · rw [if_pos arity] at success
                obtain ⟨parameter, parameters_eq⟩ :=
                  list_eq_singleton_of_length_eq_one arity
                by_cases parameter_types_eq :
                    method.parameterTypes.map
                        (TypeSystem.ParameterSubstitution.apply
                          [(parameter, operand)]) = expectedParameters
                · by_cases return_types_eq :
                      method.returnTypes.map
                          (TypeSystem.ParameterSubstitution.apply
                            [(parameter, operand)]) = expectedReturns
                  · have predicates_eq :
                        ({
                          trait
                          subject := operand
                          arguments := []
                        } : ProgramPredicate) ::
                            method.wherePredicates.map
                              (ProgramPredicate.applyParameters
                                [(parameter, operand)]) = predicates := by
                      simpa [parameters_eq, parameter_types_eq,
                        return_types_eq] using success
                    subst predicates
                    rw [← signature_facts.2]
                    exact .intro
                      (by rw [signatures_eq]; exact signature_facts.1)
                      signature_name parameters_eq methods_eq
                      parameter_types_eq return_types_eq
                  · simp [parameters_eq, parameter_types_eq,
                      return_types_eq] at success
                · simp [parameters_eq, parameter_types_eq] at success
              · rw [if_neg arity] at success
                simp at success
          | cons second tail =>
              rw [methods_eq] at success
              simp at success

/-- The operator profile selected before finalization remains valid after the
same semantic substitution used to normalize operand, result, and evidence
predicates. -/
theorem operatorTraitPredicates_instantiatesAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    {closedVariables : List TypeSystem.TypeVarId}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {operand : TypeSystem.Ty}
    {expectedParameters expectedReturns : List TypeSystem.Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid substitution
      closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (success : Detail.operatorTraitPredicates inferenceContext trait methodName
      operand expectedParameters expectedReturns = .ok predicates) :
    OperatorProfileInstantiates targetContext traitName methodName
      (substitution.apply operand)
      (expectedParameters.map substitution.apply)
      (expectedReturns.map substitution.apply)
      (predicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  apply FlexibleSubstitution.OperatorProfileInstantiates.applySubstitution
    catalog contextValid
  exact operatorTraitPredicates_instantiates signatures_eq trait_name success

/-- A profile-consistent planned coercion edge remains a declaratively valid
`Coerce` profile after the ambient inference substitution closes its endpoint
types and ordered method predicates. -/
theorem plannedCoercionStep_profileInstantiatesAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    {closedVariables : List TypeSystem.TypeVarId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {planned : Detail.PlannedCoercionStep}
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid substitution
      closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (consistent :
      Detail.PlannedCoercionStep.ProfileConsistent trait profile planned) :
    CoercionProfileInstantiates targetContext
      (substitution.apply planned.source)
      (substitution.apply planned.target)
      (TypedTraitResolution.applySubstitution substitution planned.predicate)
      (planned.methodPredicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  have raw : CoercionProfileInstantiates sourceContext planned.source
      planned.target planned.predicate planned.methodPredicates := by
    simpa [consistent.predicate_eq] using
      coercionMethodProfile?_some_instantiates signatures_eq trait_name
        profile_success consistent.methodPredicates_eq
  exact FlexibleSubstitution.CoercionProfileInstantiates.applySubstitution
    catalog contextValid raw

/-- A successful executable candidate check retains a declaratively
admissible occurrence of the candidate signature.  Argument fitting,
expected-type fitting, predicate validation, and ledger allocation happen
after the canonical fresh generic instantiation and cannot replace it. -/
theorem tryFunctionCandidate_instantiationAdmissible
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (member : signature ∈ semanticContext.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    DeclarationInstantiation.Admissible semanticContext
      result.instantiation := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  exact DeclarationInstantiation.ofInstantiated_admissible catalog binders
    residual member state.inference.next

/-- The retained candidate instantiation also supplies the exact declarative
application profile needed by the direct-call typing rule.  Its parameter row
and result are the catalog projections under the one shared fresh rigid
substitution; later argument/result fitting is deliberately outside this raw
application fact. -/
theorem tryFunctionCandidate_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (member : signature ∈ semanticContext.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    DeclarationApplicationValid semanticContext result.instantiation
      (signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          (signature.scheme.instantiate
            state.inference.next).parameterSubstitution))
      ((signature.scheme.instantiate state.inference.next)
        |>.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes))
      (signature.scheme.instantiate state.inference.next).predicates := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  let instantiated := signature.scheme.instantiate state.inference.next
  refine .intro member
    (DeclarationInstantiation.ofInstantiated_admissible catalog binders
      residual member state.inference.next) rfl rfl rfl ?_ rfl
  change instantiated.body = .function
    (TypeSystem.Ty.productMany
      (signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          instantiated.parameterSubstitution)))
    (instantiated.parameterSubstitution.apply
      (TypeSystem.Ty.productMany signature.returnTypes))
  rw [Frontend.ConstrainedDeclarationScheme.instantiate_body,
    (catalog.functions_semantic signature member).scheme_body,
    StructuralSubstitution.apply_function,
    StructuralSubstitution.apply_productMany]

/-- Fresh generic instantiation preserves admissibility of every function
parameter exposed to argument fitting. -/
theorem instantiatedFunctionParameterTypesAdmissible
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ semanticContext.signatures.functions)
    (next : Nat) :
    ∀ type, type ∈ signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          (signature.scheme.instantiate next).parameterSubstitution) →
      TypeAdmissible semanticContext type := by
  intro type typeMember
  rcases List.mem_map.mp typeMember with ⟨rawType, rawMember, rfl⟩
  have signatureWellFormed := catalog.functions_semantic signature member
  exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
    (source := signatureContext semanticContext.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates)
    (target := semanticContext)
    (signature.scheme.instantiate next).parameterSubstitution
    (DeclarationInstantiation.instantiate_parameterSubstitution_exact
      signature.scheme next
      (catalog.function_parameters signature member).1)
    (DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
      binders residual signature.scheme next)
    rfl binders (signatureWellFormed.parameter_types rawType rawMember).typeWellScoped

/-- The bundled result of a fresh generic function instantiation is
admissible before overload-result or contextual coercions are attached. -/
theorem instantiatedFunctionResultTypeAdmissible
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ semanticContext.signatures.functions)
    (next : Nat) :
    TypeAdmissible semanticContext
      ((signature.scheme.instantiate next).parameterSubstitution.apply
        (TypeSystem.Ty.productMany signature.returnTypes)) := by
  have signatureWellFormed := catalog.functions_semantic signature member
  exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
    (source := signatureContext semanticContext.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates)
    (target := semanticContext)
    (signature.scheme.instantiate next).parameterSubstitution
    (DeclarationInstantiation.instantiate_parameterSubstitution_exact
      signature.scheme next
      (catalog.function_parameters signature member).1)
    (DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
      binders residual signature.scheme next)
    rfl binders
    (StructuralSubstitution.TypesWellScoped.productMany
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
        signatureWellFormed.return_types))

/-- A successful overload selection comes from one semantic-catalog member
in the supplied candidate list and retains that member's exact declarative
application profile.  This theorem intentionally forgets ranking optimality;
only origin and static validity are needed by direct-call typing. -/
theorem selectFunctionCandidateFrom_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (candidates_subset : candidates ⊆
      semanticContext.signatures.functions)
    (success : Detail.selectFunctionCandidateFrom inferenceContext name
      candidates arguments integerLiteralOrigins call expected state =
        .ok result) :
    ∃ signature, signature ∈ candidates ∧
      DeclarationApplicationValid semanticContext result.instantiation
        (signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            (signature.scheme.instantiate
              state.inference.next).parameterSubstitution))
        ((signature.scheme.instantiate state.inference.next)
          |>.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes))
        (signature.scheme.instantiate state.inference.next).predicates := by
  obtain ⟨signature, member, candidateSuccess⟩ :=
    Detail.selectFunctionCandidateFrom_success_candidate success
  refine ⟨signature, member, ?_⟩
  exact tryFunctionCandidate_declarationApplicationValid catalog binders
    residual (candidates_subset member) candidateSuccess

/-- Ordinary unqualified overload selection inherits the same declarative
application guarantee because successful visible-name lookup returns only
members of the inference catalog.  Catalog equality transports that origin
to the semantic context used by source typing. -/
theorem selectFunctionCandidate_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {name : String} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (signatures_eq : semanticContext.signatures =
      inferenceContext.signatures)
    (success : Detail.selectFunctionCandidate inferenceContext name arguments
      integerLiteralOrigins call expected state = .ok result) :
    ∃ signature, signature ∈ semanticContext.signatures.functions ∧
      DeclarationApplicationValid semanticContext result.instantiation
        (signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            (signature.scheme.instantiate
              state.inference.next).parameterSubstitution))
        ((signature.scheme.instantiate state.inference.next)
          |>.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes))
        (signature.scheme.instantiate state.inference.next).predicates := by
  unfold Detail.selectFunctionCandidate at success
  cases candidatesResult : Detail.functionsNamed inferenceContext name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      have selection : Detail.selectFunctionCandidateFrom inferenceContext
          name candidates arguments integerLiteralOrigins call expected state =
          .ok result := by
        simpa [candidatesResult, bind, Except.bind] using success
      have inferenceSubset :=
        Detail.functionsNamed_success_subset_catalog candidatesResult
      have semanticSubset : candidates ⊆
          semanticContext.signatures.functions := by
        intro signature member
        rw [signatures_eq]
        exact inferenceSubset member
      obtain ⟨signature, member, valid⟩ :=
        selectFunctionCandidateFrom_declarationApplicationValid catalog
          binders residual semanticSubset selection
      exact ⟨signature, semanticSubset member, valid⟩

private theorem requirementId_beq_iff_eq
    (left right : RequirementId) :
    (left == right) = true ↔ left = right := by
  rw [show (left == right) = (left.index == right.index) by rfl]
  rw [beq_iff_eq]
  constructor
  · intro indices_eq
    cases left
    cases right
    cases indices_eq
    rfl
  · intro same
    exact congrArg RequirementId.index same

private theorem requirementId_contains_iff_mem
    (id : RequirementId) (ids : List RequirementId) :
    ids.contains id = true ↔ id ∈ ids := by
  induction ids with
  | nil => simp
  | cons head tail induction =>
      rw [List.contains_cons, List.mem_cons]
      rw [Bool.or_eq_true, requirementId_beq_iff_eq, induction]

/-- Successful normalized predicate solving retains declaratively valid
evidence.  The available assumptions are normalized exactly once by the same
inference substitution used by the executable solver. -/
theorem solveNormalizedPredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {goal : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solveNormalizedPredicate context state goal =
      .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules goal retained := by
  unfold Detail.solveNormalizedPredicate at success
  cases assumed : Detail.requirementAssumption? context state goal with
  | true =>
      simp only [assumed, ↓reduceIte, Except.ok.injEq] at success
      subst retained
      apply RetainedEvidenceValid.intro (.assumption goal)
      apply EvidenceValid.assumption
      unfold Detail.requirementAssumption? at assumed
      obtain ⟨assumption, member, equal⟩ := List.any_eq_true.mp assumed
      apply List.mem_map.mpr
      exact ⟨assumption, member, of_decide_eq_true equal⟩
  | false =>
      cases resolved : TypedTraitResolution.resolve
          context.signatures.resolutionRules context.traitDepth goal with
      | mk outcome statistics =>
          cases outcome with
          | noSolution =>
              simp [assumed, resolved] at success
          | inconclusive reason =>
              simp [assumed, resolved] at success
          | success evidence =>
              simp [assumed, resolved] at success
              subst retained
              apply RetainedEvidenceValid.weakenAssumptions
                (smaller := [])
              · simp
              · exact
                  TraitResolutionSoundness.resolve_success_retainedEvidenceValid
                    (rules := context.signatures.resolutionRules)
                    (maxDepth := context.traitDepth)
                    (goal := goal)
                    (retained := evidence)
                    (by simp [resolved])

/-- `solvePredicate` first normalizes its source predicate and then delegates
to `solveNormalizedPredicate`, so its successful result has the same retained
evidence guarantee at the normalized goal. -/
theorem solvePredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solvePredicate context state source = .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules
      (Detail.applyPredicate state source) retained := by
  exact solveNormalizedPredicate_sound success

/-- An ordinary solved ledger row inherits the predicate solver's evidence
validity once the executable and declarative contexts agree on the catalog and
on the normalized declaration assumptions. -/
theorem solveRequirementEvidence_ordinary_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    {semanticContext : SourceSemantics.Context}
    (ordinary : requirement.id ∉ state.localSchemeAssumptions)
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (success : Detail.solveRequirementEvidence inferenceContext state
      requirement = .ok retained) :
    SolvedRequirementValid semanticContext {
      id := requirement.id
      predicate := Detail.applyPredicate state requirement.predicate
      evidence := retained
    } := by
  have ordinaryContains :
      state.localSchemeAssumptions.contains requirement.id = false := by
    cases containsEq : state.localSchemeAssumptions.contains requirement.id with
    | false => rfl
    | true =>
        exact False.elim
          (ordinary ((requirementId_contains_iff_mem _ _).mp containsEq))
  have normalizedSuccess :
      Detail.solveNormalizedPredicate inferenceContext state
          (Detail.applyPredicate state requirement.predicate) = .ok retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [ordinaryContains] at success
    simpa using success
  apply SolvedRequirementValid.intro
  rw [signatures_eq, assumptions_eq]
  exact solveNormalizedPredicate_sound normalizedSuccess

/-- Qualified-local template rows bypass trait search and retain exactly an
assumption for their normalized predicate. -/
theorem solveRequirementEvidence_template_eq
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    (template : requirement.id ∈ state.localSchemeAssumptions)
    (success : Detail.solveRequirementEvidence context state requirement =
      .ok retained) :
    retained = .assumption
      (Detail.applyPredicate state requirement.predicate) := by
  have templateContains :
      state.localSchemeAssumptions.contains requirement.id = true := by
    exact (requirementId_contains_iff_mem _ _).mpr template
  have retainedEq :
      (.assumption (Detail.applyPredicate state requirement.predicate) :
        PredicateEvidence) = retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [templateContains] at success
    change Except.ok (.assumption
      (Detail.applyPredicate state requirement.predicate)) =
        Except.ok retained at success
    exact Except.ok.inj success
  exact retainedEq.symm

/-- Successful ledger solving preserves source order and records, for every
output row, its exact input identity, normalized predicate, and evidence-solver
equation. -/
theorem solveRequirements_corresponds
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (success : Detail.solveRequirements context state requirements =
      .ok solved) :
    Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence context state requirement =
          .ok row.evidence) requirements solved := by
  induction requirements generalizing solved with
  | nil =>
      simp only [Detail.solveRequirements, Except.ok.injEq] at success
      subst solved
      exact .nil
  | cons requirement rest induction =>
      cases evidenceResult :
          Detail.solveRequirementEvidence context state requirement with
      | error error =>
          simp [Detail.solveRequirements, evidenceResult, bind, Except.bind]
            at success
      | ok evidence =>
          cases tailResult : Detail.solveRequirements context state rest with
          | error error =>
              simp [Detail.solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at success
          | ok tail =>
              let solvedHead : SolvedRequirement := {
                id := requirement.id
                predicate := Detail.applyPredicate state requirement.predicate
                evidence := evidence
              }
              simp [Detail.solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at success
              subst solved
              exact .cons (by simp [evidenceResult])
                (induction tailResult)

private theorem solved_row_of_requirement_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence inferenceContext state requirement =
          .ok row.evidence) requirements solved)
    {requirement : Requirement}
    (member : requirement ∈ requirements) :
    ∃ row, row ∈ solved ∧
      row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction corresponds with
  | nil => simp at member
  | @cons head row tail rows headCorresponds tailCorresponds induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨row, by simp, headCorresponds.1, headCorresponds.2.1⟩
      · obtain ⟨found, foundMember, idEq, predicateEq⟩ := induction member
        exact ⟨found, by simp [foundMember], idEq, predicateEq⟩

/-- Every identity in a successfully solved input ledger names independently
valid evidence in the corresponding declarative solved ledger. -/
theorem solveRequirements_requirementIdsValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementIdsValid semanticContext (requirements.map (·.id)) := by
  intro id member
  obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, idEq, predicateEq⟩ :=
    solved_row_of_requirement_mem (solveRequirements_corresponds success)
      requirementMember
  exact ⟨Detail.applyPredicate state requirement.predicate, row,
    ⟨by simpa [solved_eq] using rowMember, idEq⟩, predicateEq,
    valid row rowMember⟩

/-- Any occurrence-owned identity subset of a successfully solved input
ledger is independently valid in the corresponding declarative context. -/
theorem solveRequirements_requirementIdsValid_of_subset
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {ids : List RequirementId}
    (included : ids ⊆ requirements.map (·.id))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementIdsValid semanticContext ids :=
  RequirementIdsValid.of_subset included
    (solveRequirements_requirementIdsValid success solved_eq valid)

/-- A source-ordered predicate/identity correspondence into a successfully
solved final ledger supplies the declarative evidence sequence for exactly
those normalized predicates. -/
theorem solveRequirements_correspondingSequenceProves
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {predicates : List ProgramPredicate}
    {ids : List RequirementId}
    (corresponds : RequirementPredicatesCorrespond requirements predicates ids)
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementSequenceProves semanticContext ids
      (predicates.map (Detail.applyPredicate state)) := by
  have solverCorresponds := solveRequirements_corresponds success
  clear success
  induction corresponds with
  | nil => exact .nil
  | @cons predicate id predicates ids member tail induction =>
      apply RequirementSequenceProves.cons
      · obtain ⟨row, rowMember, idEq, predicateEq⟩ :=
          solved_row_of_requirement_mem solverCorresponds member
        exact ⟨row, ⟨by simpa [solved_eq] using rowMember, idEq⟩,
          predicateEq, valid row rowMember⟩
      · exact induction

/-- Decoding, final carrier closure, exact ledger ownership, and solver
soundness compose into the declarative validity judgment for one inferred
integer literal. -/
theorem integerLiteralValid_of_solved
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (decoded : Frontend.numericLiteralValue? source = some resolution.rawValue)
    (target_supported :
      (resolution.applySubstitution state.inference.substitution).targetType =
          .word ∨
        (resolution.applySubstitution state.inference.substitution).targetType =
          .integer)
    (requirement_mem :
      ({ id := resolution.requirement, predicate := resolution.predicate } :
        Requirement) ∈ state.requirements)
    (solve_success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    IntegerLiteralValid semanticContext source
      (resolution.applySubstitution state.inference.substitution) := by
  have proves : RequirementSequenceProves semanticContext
      [resolution.requirement] [Detail.applyPredicate state
        resolution.predicate] :=
    solveRequirements_correspondingSequenceProves
      (.cons requirement_mem .nil) solve_success solved_eq valid
  have evidence : RequirementProves semanticContext
      (resolution.applySubstitution state.inference.substitution).requirement
      (resolution.applySubstitution state.inference.substitution).predicate := by
    rw [IntegerLiteralResolution.applySubstitution_requirement,
      IntegerLiteralResolution.applySubstitution_predicate]
    simpa [Detail.applyPredicate] using proves.head
  have meaning : Frontend.NumericLiteralDenotes source
      (resolution.applySubstitution state.inference.substitution).rawValue := by
    simpa using Frontend.numericLiteralValue?_sound decoded
  rcases target_supported with target_eq | target_eq
  · exact .word meaning target_eq
      (by simpa [IntegerLiteralResolution.predicate] using evidence)
  · exact .integer meaning target_eq
      (by simpa [IntegerLiteralResolution.predicate] using evidence)

/-- A validated unary trait profile and its source-ordered rows in the final
solved ledger assemble the declarative unary-operator judgment after applying
the final inference substitution. -/
theorem unaryOperatorTrait_hasTypeAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {state : Frontend.SourceInference.State}
    {closedVariables : List TypeSystem.TypeVarId}
    {solved : List SolvedRequirement}
    {operator : Syntax.UnaryOp} {trait : Resolved.DeclarationId}
    {traitName methodName : String} {operand result : TypeSystem.Ty}
    {predicates : List ProgramPredicate} {requirements : List RequirementId}
    (dispatch : UnaryTraitDispatch operator traitName methodName)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      state.inference.substitution closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (profile_success : Detail.operatorTraitPredicates inferenceContext trait
      methodName operand [operand] [result] = .ok predicates)
    (corresponds : RequirementPredicatesCorrespond state.requirements
      predicates requirements)
    (solve_success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved)
    (solved_eq : targetContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid targetContext solved) :
    UnaryOperatorHasType targetContext operator
      (state.inference.substitution.apply operand)
      (state.inference.substitution.apply result) requirements := by
  apply UnaryOperatorHasType.trait dispatch
  · simpa using
      operatorTraitPredicates_instantiatesAfterSubstitution catalog contextValid
        signatures_eq trait_name profile_success
  · change RequirementSequenceProves targetContext requirements
      (predicates.map (Detail.applyPredicate state))
    exact solveRequirements_correspondingSequenceProves corresponds
      solve_success solved_eq valid

/-- Binary trait inference has the analogous composition: a validated
two-operand profile plus the corresponding solved ledger rows yields the
declarative binary-operator judgment under the final substitution. -/
theorem binaryOperatorTrait_hasTypeAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {state : Frontend.SourceInference.State}
    {closedVariables : List TypeSystem.TypeVarId}
    {solved : List SolvedRequirement}
    {operator : Syntax.BinaryOp} {trait : Resolved.DeclarationId}
    {traitName methodName : String} {operand result : TypeSystem.Ty}
    {predicates : List ProgramPredicate} {requirements : List RequirementId}
    (dispatch : BinaryTraitDispatch operator traitName methodName)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      state.inference.substitution closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (profile_success : Detail.operatorTraitPredicates inferenceContext trait
      methodName operand [operand, operand] [result] = .ok predicates)
    (corresponds : RequirementPredicatesCorrespond state.requirements
      predicates requirements)
    (solve_success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved)
    (solved_eq : targetContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid targetContext solved) :
    BinaryOperatorHasType targetContext operator
      (state.inference.substitution.apply operand)
      (state.inference.substitution.apply operand)
      (state.inference.substitution.apply result) requirements := by
  apply BinaryOperatorHasType.trait dispatch
  · simpa using
      operatorTraitPredicates_instantiatesAfterSubstitution catalog contextValid
        signatures_eq trait_name profile_success
  · change RequirementSequenceProves targetContext requirements
      (predicates.map (Detail.applyPredicate state))
    exact solveRequirements_correspondingSequenceProves corresponds
      solve_success solved_eq valid

/-- A committed coercion edge inherits the primary and method evidence rows
owned by its planned edge, in the exact order expected by
`CoercionStepValid`. -/
theorem solveRequirements_committedCoercionStepSequenceProves
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {planned : Detail.PlannedCoercionStep}
    {committed : CoercionStep}
    (corresponds : Detail.PlannedCoercionStep.CommitCorresponds requirements
      planned committed)
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementSequenceProves semanticContext
      (committed.requirement :: committed.methodRequirements)
      (Detail.applyPredicate state planned.predicate ::
        planned.methodPredicates.map (Detail.applyPredicate state)) := by
  apply RequirementSequenceProves.cons
  · have primaryCorresponds : RequirementPredicatesCorrespond requirements
        [planned.predicate] [committed.requirement] :=
      .cons corresponds.primary_mem .nil
    exact (solveRequirements_correspondingSequenceProves primaryCorresponds
      success solved_eq valid).head
  · exact solveRequirements_correspondingSequenceProves
      corresponds.methods success solved_eq valid

/-- Once its normalized profile and solved ledger are valid, a committed
frontend edge is a declaratively valid coercion step after applying the same
inference substitution used to normalize its requirements. -/
theorem committedCoercionStepValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {planned : Detail.PlannedCoercionStep}
    {committed : CoercionStep}
    (corresponds : Detail.PlannedCoercionStep.CommitCorresponds requirements
      planned committed)
    (profile : CoercionProfileInstantiates semanticContext
      (state.resolve planned.source) (state.resolve planned.target)
      (Detail.applyPredicate state planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate state)))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionStepValid semanticContext
      (committed.applySubstitution state.inference.substitution) := by
  apply CoercionStepValid.intro
      (primary := Detail.applyPredicate state planned.predicate)
      (methodPredicates :=
        planned.methodPredicates.map (Detail.applyPredicate state))
  · simpa [CoercionStep.applySubstitution, State.resolve,
      TypeSystem.InferState.resolve, corresponds.source_eq,
      corresponds.target_eq] using profile
  · simpa [CoercionStep.applySubstitution] using
      solveRequirements_committedCoercionStepSequenceProves corresponds
        success solved_eq valid

private theorem committed_member_has_planned_correspondence
    {requirements : List Requirement}
    {plan : List Detail.PlannedCoercionStep}
    {steps : List CoercionStep}
    (corresponds : Detail.CoercionPlanCommitCorresponds requirements
      plan steps)
    {committed : CoercionStep}
    (member : committed ∈ steps) :
    ∃ planned, planned ∈ plan ∧
      Detail.PlannedCoercionStep.CommitCorresponds requirements
        planned committed := by
  induction corresponds with
  | nil => simp at member
  | @cons planned committed plan steps head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨planned, by simp, head⟩
      · obtain ⟨candidate, candidateMember, candidateCorresponds⟩ :=
          induction member
        exact ⟨candidate, by simp [candidateMember], candidateCorresponds⟩

/-- Structural search validity, exact commit correspondence, normalized
profile validity for every planned edge, and a valid solved ledger compose to
the declarative validity of the complete committed coercion path. -/
theorem committedCoercionPlanValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (structural : Detail.PlannedCoercionPath.isValid source target plan = true)
    (profiles : ∀ planned, planned ∈ plan →
      CoercionProfileInstantiates semanticContext
        ((Detail.commitCoercionPlan state plan).2.resolve planned.source)
        ((Detail.commitCoercionPlan state plan).2.resolve planned.target)
        (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2
          planned.predicate)
        (planned.methodPredicates.map
          (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2)))
    (success : Detail.solveRequirements inferenceContext
      (Detail.commitCoercionPlan state plan).2
      (Detail.commitCoercionPlan state plan).2.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      ((Detail.commitCoercionPlan state plan).2.resolve source)
      ((Detail.commitCoercionPlan state plan).2.resolve target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          (Detail.commitCoercionPlan state plan).2.inference.substitution)) := by
  let committed := Detail.commitCoercionPlan state plan
  have committedStructural :
      Frontend.SourceInference.CoercionPath.isValid source target
        committed.1 = true :=
    Detail.commitCoercionPlan_isValid state plan structural
  have normalizedStructural :
      Frontend.SourceInference.CoercionPath.isValid
        (committed.2.resolve source) (committed.2.resolve target)
        (committed.1.map
          (CoercionStep.applySubstitution
            committed.2.inference.substitution)) = true := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
      Frontend.SourceInference.CoercionPath.isValid_applySubstitution
        committed.2.inference.substitution committedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp stepMember
  have correspondences := Detail.commitCoercionPlan_corresponds state plan
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence correspondences originalMember
  exact committedCoercionStepValid correspondence
    (profiles planned plannedMember) success solved_eq valid

/-- Successful coercion planning, profile lookup, commit, and requirement
solving form a declaratively valid normalized coercion path once the final
inference substitution is a valid semantic context closure. -/
theorem coercionPlan?_some_committedPathValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {sourceContext semanticContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (trait_success :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (plan_success :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      (Detail.commitCoercionPlan state plan).2.inference.substitution
      closedVariables sourceContext semanticContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solve_success : Detail.solveRequirements inferenceContext
      (Detail.commitCoercionPlan state plan).2
      (Detail.commitCoercionPlan state plan).2.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      ((Detail.commitCoercionPlan state plan).2.resolve source)
      ((Detail.commitCoercionPlan state plan).2.resolve target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          (Detail.commitCoercionPlan state plan).2.inference.substitution)) := by
  apply committedCoercionPlanValid
      (Detail.coercionPlan?_some_isValid plan_success) ?_ solve_success
      solved_eq valid
  intro planned member
  have consistent := Detail.coercionPlan?_some_profileConsistent
    trait_success profile_success plan_success planned member
  have methodPredicates_eq :
      planned.methodPredicates.map
          (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2) =
        planned.methodPredicates.map
          (TypedTraitResolution.applySubstitution
            (Detail.commitCoercionPlan state plan).2.inference.substitution) := by
    apply List.map_congr_left
    intro predicate predicateMember
    rfl
  rw [methodPredicates_eq]
  simpa [Frontend.SourceInference.State.resolve,
    TypeSystem.InferState.resolve, Detail.applyPredicate] using
    plannedCoercionStep_profileInstantiatesAfterSubstitution
      (substitution :=
        (Detail.commitCoercionPlan state plan).2.inference.substitution)
      catalog contextValid signatures_eq trait_name profile_success consistent

/-- A committed coercion plan remains semantically valid when later inference
extends its requirement ledger and the whole enlarged ledger is solved under a
later closing substitution.  This is the form needed by expression inference:
coercions are committed locally, but their evidence is solved only after the
rest of the declaration has been traversed. -/
theorem coercionPlan?_some_committedPathValid_at
    {inferenceContext : Frontend.SourceInference.Context}
    {state later : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {sourceContext semanticContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (trait_success :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (plan_success :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (requirements_subset :
      (Detail.commitCoercionPlan state plan).2.requirements ⊆
        later.requirements)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext
        semanticContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solve_success : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution)) := by
  have corresponds : Detail.CoercionPlanCommitCorresponds later.requirements
      plan (Detail.commitCoercionPlan state plan).1 :=
    (Detail.commitCoercionPlan_corresponds state plan).mono
      requirements_subset
  have retainedStructural : Frontend.SourceInference.CoercionPath.isValid
      source target (Detail.commitCoercionPlan state plan).1 = true :=
    corresponds.isValid (Detail.coercionPlan?_some_isValid plan_success)
  have normalizedStructural : Frontend.SourceInference.CoercionPath.isValid
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution)) = true :=
    Frontend.SourceInference.CoercionPath.isValid_applySubstitution
      later.inference.substitution retainedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨committed, committedMember, rfl⟩ := List.mem_map.mp stepMember
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence corresponds committedMember
  have consistent := Detail.coercionPlan?_some_profileConsistent
    trait_success profile_success plan_success planned plannedMember
  have methodPredicates_eq :
      planned.methodPredicates.map (Detail.applyPredicate later) =
        planned.methodPredicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate predicateMember
    rfl
  have profile :=
    plannedCoercionStep_profileInstantiatesAfterSubstitution
      (substitution := later.inference.substitution) catalog contextValid
      signatures_eq trait_name profile_success consistent
  have normalizedProfile : CoercionProfileInstantiates semanticContext
      (later.resolve planned.source) (later.resolve planned.target)
      (Detail.applyPredicate later planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate later)) := by
    rw [methodPredicates_eq]
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve, Detail.applyPredicate] using profile
  exact committedCoercionStepValid (state := later) correspondence
    normalizedProfile solve_success solved_eq valid

/-- Expected-type fitting yields a semantically valid output-coercion path
after the enclosing inference traversal has finished.  An absent expectation
or successful unification gives the empty path; a mismatch reuses the exact
planned and committed path exposed by `withExpected_success_cases`. -/
theorem withExpected_success_coercionPathValid_afterFinalization
    {inferenceContext : Frontend.SourceInference.Context}
    {state later : Frontend.SourceInference.State}
    {actual : InferredExpression}
    {expected : Option TypeSystem.Ty}
    {result : Detail.ExpectationResult}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext semanticContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (success : Detail.withExpected inferenceContext state actual expected =
      .ok result)
    (trait_success :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (requirements_subset : result.state.requirements ⊆ later.requirements)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext
        semanticContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solve_success : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      (later.inference.substitution.apply
        (result.state.resolve actual.type))
      (later.inference.substitution.apply result.expression.type)
      (result.coercions.map
        (CoercionStep.applySubstitution later.inference.substitution)) := by
  rcases Detail.withExpected_success_cases success with
    ⟨coercions_eq, requirements_eq, type_eq⟩ |
      ⟨expectedType, plan, expected_eq, plan_success, result_eq⟩
  · rw [coercions_eq]
    simp only [List.map_nil]
    rw [type_eq]
    exact .nil _
  · subst expected
    subst result
    change CoercionPathValid semanticContext
      (later.inference.substitution.apply
        ((Detail.commitCoercionPlan state plan).2.resolve actual.type))
      (later.inference.substitution.apply (state.resolve expectedType))
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution))
    rw [Detail.commitCoercionPlan_resolve]
    exact coercionPlan?_some_committedPathValid_at trait_success
      profile_success plan_success requirements_subset catalog contextValid
      signatures_eq trait_name solve_success solved_eq valid

/-- Every solved row classified as a qualified-local template by the input
state retains the canonical assumption evidence for its normalized
predicate. -/
theorem solveRequirements_template_evidence
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (success : Detail.solveRequirements context state requirements =
      .ok solved) :
    ∀ row, row ∈ solved → row.id ∈ state.localSchemeAssumptions →
      row.evidence = .assumption row.predicate := by
  have corresponds := solveRequirements_corresponds success
  clear success
  induction corresponds with
  | nil =>
      intro row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro candidate member template
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        have requirement_template :
            requirement.id ∈ state.localSchemeAssumptions := by
          rw [← id_eq]
          exact template
        have evidence_eq := solveRequirementEvidence_template_eq
          requirement_template evidence_success
        rw [predicate_eq]
        exact evidence_eq
      · exact induction candidate member template

/-- When no input row is a qualified-local template, successful ledger
solving validates every output row in a declarative context with the same
catalog and normalized declaration assumptions. -/
theorem solveRequirements_ordinary_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (ordinary : ∀ requirement, requirement ∈ requirements →
      requirement.id ∉ state.localSchemeAssumptions)
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved) :
    SolvedRequirementsValid semanticContext solved := by
  have corresponds := solveRequirements_corresponds success
  clear success
  unfold SolvedRequirementsValid
  revert ordinary
  induction corresponds with
  | nil =>
      intro _ row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro ordinary candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        have valid := solveRequirementEvidence_ordinary_sound
          (semanticContext := semanticContext)
          (ordinary requirement (by simp)) signatures_eq assumptions_eq
          evidence_success
        have candidate_eq : candidate = {
            id := requirement.id
            predicate := Detail.applyPredicate state requirement.predicate
            evidence := candidate.evidence
          } := by
          cases candidate
          simp_all
        rw [candidate_eq]
        exact valid
      · exact induction (fun tailRequirement tailMember =>
          ordinary tailRequirement (by simp [tailMember])) candidate member

/-- Successful ledger solving validates ordinary rows through retained trait
evidence and qualified-local template rows through their exact
initializer-scoped source ownership. -/
theorem solveRequirements_scoped_entries_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {source : TypedSource}
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (template_iff : ∀ requirement, requirement ∈ requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (template_scoped : ∀ requirement, requirement ∈ requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved) :
    ∀ row, row ∈ solved →
      ScopedRequirementEntryValid semanticContext source row := by
  have corresponds := solveRequirements_corresponds success
  clear success
  revert template_iff template_scoped
  induction corresponds with
  | nil =>
      intro _ _ row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro template_iff template_scoped candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        by_cases template : requirement.id ∈ state.localSchemeAssumptions
        · have evidence_eq := solveRequirementEvidence_template_eq template
            evidence_success
          have candidate_eq : candidate = {
              id := requirement.id
              predicate := Detail.applyPredicate state requirement.predicate
              evidence := .assumption
                (Detail.applyPredicate state requirement.predicate)
            } := by
            cases candidate
            simp_all
          rw [candidate_eq]
          exact .template (template_scoped requirement (by simp) template)
        · have valid := solveRequirementEvidence_ordinary_sound
            (semanticContext := semanticContext) template signatures_eq
            assumptions_eq evidence_success
          have not_template : requirement.id ∉
              sourceLocalSchemeTemplateIds source := by
            intro source_member
            exact template ((template_iff requirement (by simp)).mpr
              source_member)
          have candidate_eq : candidate = {
              id := requirement.id
              predicate := Detail.applyPredicate state requirement.predicate
              evidence := candidate.evidence
            } := by
            cases candidate
            simp_all
          rw [candidate_eq]
          exact .ordinary not_template valid
      · exact induction
          (fun tailRequirement tailMember =>
            template_iff tailRequirement (by simp [tailMember]))
          (fun tailRequirement tailMember template =>
            template_scoped tailRequirement (by simp [tailMember]) template)
          candidate member

/-- A duplicate-free inference ledger with complete source-template coverage
becomes a whole-body scoped requirement ledger after successful solving. -/
theorem solveRequirements_scoped_ledger_sound_of_nodup
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {baseContext : SourceSemantics.Context}
    {source : TypedSource}
    (ledgerUnique :
      (state.requirements.map fun requirement => requirement.id).Nodup)
    (signatures_eq : baseContext.signatures = inferenceContext.signatures)
    (assumptions_eq : baseContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (templateOwnership : LocalSchemeTemplateOwnership source)
    (template_iff : ∀ requirement, requirement ∈ state.requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (templates_subset : sourceLocalSchemeTemplateIds source ⊆
      state.requirements.map (fun requirement => requirement.id))
    (template_scoped : ∀ requirement, requirement ∈ state.requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved) :
    ScopedRequirementLedgerWellFormed
      (baseContext.withSolvedRequirements solved) source := by
  refine {
    idsUnique := ?_
    templateOwnership := templateOwnership
    entriesValid := ?_
    templatesComplete := ?_
  }
  · change (solved.map (fun requirement => requirement.id)).Nodup
    rw [Detail.solveRequirements_preserves_ids inferenceContext state
      state.requirements solved success]
    exact ledgerUnique
  · exact solveRequirements_scoped_entries_sound
      (semanticContext := baseContext.withSolvedRequirements solved)
      signatures_eq assumptions_eq template_iff template_scoped success
  · intro owner contains
    have templateMember : owner.requirement.templateRequirement ∈
        sourceLocalSchemeTemplateIds source :=
      sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
    have inputMember : owner.requirement.templateRequirement ∈
        state.requirements.map (fun requirement => requirement.id) :=
      templates_subset templateMember
    have ids_eq := Detail.solveRequirements_preserves_ids inferenceContext state
      state.requirements solved success
    have outputMember : owner.requirement.templateRequirement ∈
        solved.map (fun requirement => requirement.id) := by
      rw [ids_eq]
      exact inputMember
    rcases List.mem_map.mp outputMember with ⟨row, member, id_eq⟩
    exact ⟨row, member, id_eq⟩

/-- Compatibility form deriving duplicate-free raw requirement identities
from the canonical allocation invariant. -/
theorem solveRequirements_scoped_ledger_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {baseContext : SourceSemantics.Context}
    {source : TypedSource}
    (stateWellFormed : state.RequirementsWellFormed)
    (signatures_eq : baseContext.signatures = inferenceContext.signatures)
    (assumptions_eq : baseContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (templateOwnership : LocalSchemeTemplateOwnership source)
    (template_iff : ∀ requirement, requirement ∈ state.requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (templates_subset : sourceLocalSchemeTemplateIds source ⊆
      state.requirements.map (fun requirement => requirement.id))
    (template_scoped : ∀ requirement, requirement ∈ state.requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved) :
    ScopedRequirementLedgerWellFormed
      (baseContext.withSolvedRequirements solved) source := by
  apply solveRequirements_scoped_ledger_sound_of_nodup
    (Frontend.SourceInference.State.requirementIds_nodup state stateWellFormed)
    signatures_eq assumptions_eq templateOwnership template_iff
    templates_subset template_scoped success

/-- Qualified-local template identities materialized directly by one source
node.  Expression nodes never materialize binders; statement nodes may retain
an initialized `let` directly or in a `for` header. -/
def nodeLocalSchemeTemplateIds : Node → List RequirementId
  | .expression _ => []
  | .statement statement =>
      (statementInitializedLetBindings statement.form).flatMap fun binding =>
        binding.binder.schemeRequirements.map
          (fun requirement => requirement.templateRequirement)

/-- Appending one node appends exactly that node's qualified-local template
identity inventory. -/
theorem recordNode_sourceLocalSchemeTemplateIds
    (state : Frontend.SourceInference.State) (node : Node)
    (roots : List NodeId) :
    sourceLocalSchemeTemplateIds ((state.recordNode node).toTypedSource roots) =
      sourceLocalSchemeTemplateIds (state.toTypedSource roots) ++
        nodeLocalSchemeTemplateIds node := by
  cases node with
  | expression expression =>
      simp [Frontend.SourceInference.State.recordNode,
        Frontend.SourceInference.State.toTypedSource,
        sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings, nodeLocalSchemeTemplateIds]
  | statement statement =>
      simp [Frontend.SourceInference.State.recordNode,
        Frontend.SourceInference.State.toTypedSource,
        sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings, InitializedLetBinding.templateOwners,
        nodeLocalSchemeTemplateIds, List.map_flatMap,
        List.map_map, Function.comp_def]

/-- ID-only ghost invariant for source-inference template tracking.  The
`pending` suffix contains template identities allocated into binders whose
owning statement node has not yet been recorded. -/
structure TemplateTracking (state : Frontend.SourceInference.State)
    (pending : List RequirementId) : Prop where
  classified : state.localSchemeAssumptions.Perm
    (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
  unique : state.localSchemeAssumptions.Nodup
  covered : ∀ id, id ∈ state.localSchemeAssumptions →
    id ∈ state.requirements.map (fun requirement => requirement.id)

namespace TemplateTracking

/-- Initial inference states contain neither source-owned nor pending local
scheme templates. -/
theorem initial (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment := [])
    (comptime : List Bool := []) :
    TemplateTracking
      (Frontend.SourceInference.State.initial owner locals comptime) [] := by
  constructor <;>
    simp [Frontend.SourceInference.State.initial,
      Frontend.SourceInference.State.toTypedSource,
      sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings]

/-- Executable finalization-boundary validation reconstructs the proof-facing
template tracking invariant with no pending binder materialization. -/
theorem ofValidation
    {state : Frontend.SourceInference.State} {roots : List NodeId}
    (success : Detail.validateSourceTemplateTracking
      (state.toTypedSource roots) state = .ok ()) :
    TemplateTracking state [] := by
  have validated := Detail.validateSourceTemplateTracking_success success
  constructor
  · simpa [Frontend.SourceInference.State.toTypedSource,
      sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings] using validated.2.2.1
  · exact validated.2.1
  · exact validated.2.2.2

/-- Replacing only the executable local type environment leaves template
classification, uniqueness, and requirement-ledger coverage unchanged.  This
is the exact state update performed immediately before let-binder allocation. -/
theorem replaceLocals
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (locals : TypeSystem.Environment) :
    TemplateTracking { state with locals := locals } pending := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
    exact tracked.classified
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Allocating a binder moves its qualified requirement identities into the
pending suffix.  Canonical generalization supplies the three side conditions:
new identities are distinct, fresh for the classification, and already occur
in the input requirement ledger. -/
theorem allocateBinder
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    (newUnique :
      (schemeRequirements.map (fun requirement =>
        requirement.templateRequirement)).Nodup)
    (newFresh : ∀ id, id ∈ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement) →
      id ∉ state.localSchemeAssumptions)
    (newCovered : ∀ id, id ∈ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement) →
      id ∈ state.requirements.map (fun requirement => requirement.id)) :
    TemplateTracking
      (state.allocateBinder name scheme span comptime schemeRequirements).2
      (pending ++ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement)) := by
  let added := schemeRequirements.map (fun requirement =>
    requirement.templateRequirement)
  constructor
  · change (state.localSchemeAssumptions ++ added).Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
        (pending ++ added))
    simpa only [List.append_assoc] using tracked.classified.append_right added
  · change (state.localSchemeAssumptions ++ added).Nodup
    rw [List.nodup_append]
    refine ⟨tracked.unique, (by simpa [added] using newUnique), ?_⟩
    intro old oldMember new newMember same
    subst new
    exact newFresh old (by simpa [added] using newMember) oldMember
  · intro id member
    change id ∈ state.requirements.map (fun requirement => requirement.id)
    change id ∈ state.localSchemeAssumptions ++ added at member
    rcases List.mem_append.mp member with oldMember | addedMember
    · exact tracked.covered id oldMember
    · exact newCovered id (by simpa [added] using addedMember)

/-- Canonical local generalization discharges every side condition required
by template-tracking binder allocation.  The executable let paths first
replace `locals` with its substituted form and then perform exactly this
allocation. -/
theorem allocateGeneralizedValue
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (requirementsWellFormed : state.RequirementsWellFormed)
    (locals : TypeSystem.Environment) (requirementStart : Nat)
    (type : TypeSystem.Ty) (name : String)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false) :
    let generalized := Frontend.SourceInference.Detail.generalizeValue state
      locals requirementStart type
    TemplateTracking
      (({ state with locals := locals }).allocateBinder name
        generalized.scheme span comptime generalized.requirements).2
      (pending ++ generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
  dsimp only
  apply allocateBinder (tracked.replaceLocals locals) name
    (Frontend.SourceInference.Detail.generalizeValue state locals
      requirementStart type).scheme span comptime
    (Frontend.SourceInference.Detail.generalizeValue state locals
      requirementStart type).requirements
  · exact
      (Frontend.SourceInference.Detail.generalizeValue_templateIds_sublist
        state locals requirementStart type).nodup
        (Frontend.SourceInference.State.requirementIds_nodup state
          requirementsWellFormed)
  · intro id member
    change id ∉ state.localSchemeAssumptions
    exact Frontend.SourceInference.Detail.generalizeValue_templateIds_fresh
      state locals requirementStart type id member
  · intro id member
    change id ∈ state.requirements.map (fun requirement => requirement.id)
    exact
      (Frontend.SourceInference.Detail.generalizeValue_templateIds_sublist
        state locals requirementStart type).subset member

/-- Recording a node materializes a pending suffix matching that node's exact
template inventory; older ambient pending identities remain pending. -/
theorem recordNode
    {state : Frontend.SourceInference.State}
    {ambient : List RequirementId} {node : Node}
    (tracked : TemplateTracking state
      (ambient ++ nodeLocalSchemeTemplateIds node)) :
    TemplateTracking (state.recordNode node) ambient := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds ((state.recordNode node).toTypedSource []) ++
        ambient)
    rw [recordNode_sourceLocalSchemeTemplateIds]
    have swapped :
        (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
            (ambient ++ nodeLocalSchemeTemplateIds node)).Perm
          (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
            (nodeLocalSchemeTemplateIds node ++ ambient)) :=
      List.Perm.append_left _ List.perm_append_comm
    simpa only [List.append_assoc] using tracked.classified.trans swapped
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Lexical restoration changes neither the emitted node table nor executable
template classification and therefore preserves every pending suffix. -/
theorem restoreLexicalScope
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (scope : Frontend.SourceInference.LexicalScope) :
    TemplateTracking (state.restoreLexicalScope scope) pending := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
    exact tracked.classified
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Once no template identity remains pending, the materialized source owns
globally unique qualified-template identities. -/
theorem ownership
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := []) :
    LocalSchemeTemplateOwnership (state.toTypedSource roots) := by
  constructor
  have sourceUnique :
      (sourceLocalSchemeTemplateIds (state.toTypedSource [])).Nodup := by
    simpa using tracked.classified.nodup_iff.mp tracked.unique
  simpa [Frontend.SourceInference.State.toTypedSource,
    sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings] using sourceUnique

/-- With an empty pending suffix, executable classification and materialized
source ownership classify exactly the same stable identities. -/
theorem classified_iff
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := [])
    (id : RequirementId) :
    id ∈ state.localSchemeAssumptions ↔
      id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource roots) := by
  have aligned : id ∈ state.localSchemeAssumptions ↔
      id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ [] :=
    tracked.classified.mem_iff
  simpa [Frontend.SourceInference.State.toTypedSource,
    sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings] using aligned

/-- Every fully materialized source template identity comes from an input
requirement row. -/
theorem source_ids_subset_requirements
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := []) :
    sourceLocalSchemeTemplateIds (state.toTypedSource roots) ⊆
      state.requirements.map (fun requirement => requirement.id) := by
  intro id sourceMember
  exact tracked.covered id ((tracked.classified_iff roots id).mpr sourceMember)

end TemplateTracking

/-- Every successful finalization input has a complete, unique and
ledger-covered qualified-template classification. -/
theorem finalize_templateTracking
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    TemplateTracking state [] :=
  TemplateTracking.ofValidation
    (Detail.finalize_validateSourceTemplateTracking success)

/-- Final substitution preserves the globally unique ownership of every
qualified local-scheme template retained by a finalized source. -/
theorem finalize_localSchemeTemplateOwnership
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    LocalSchemeTemplateOwnership result.typedSource := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.LocalSchemeTemplateOwnership.applySubstitution
    result.substitution ((finalize_templateTracking success).ownership roots)

/-- Successfully checked function bodies retain globally unique qualified
local-scheme template identities. -/
theorem checkFunctionBody_success_localSchemeTemplateOwnership
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    LocalSchemeTemplateOwnership checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_localSchemeTemplateOwnership finalizeSuccess

/-- The source-owned qualified-local template identities materialized from a
state agree exactly with the state's executable template classification. -/
def TemplateIdsAligned (state : Frontend.SourceInference.State)
    (roots : List NodeId) : Prop :=
  ∀ id, id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource roots) ↔
    id ∈ state.localSchemeAssumptions

/-- Final substitution preserves source template identities, so an alignment
established before finalization remains visible in the emitted typed source. -/
theorem finalize_templateIdsAligned
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (aligned : TemplateIdsAligned state roots)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ id, id ∈ sourceLocalSchemeTemplateIds result.typedSource ↔
      id ∈ state.localSchemeAssumptions := by
  intro id
  rw [Detail.finalize_typedSource success]
  simp only [FlexibleSubstitution.sourceLocalSchemeTemplateIds_applySubstitution]
  exact aligned id

/-- Successful finalization supplies template classification alignment without
an external tracking premise. -/
theorem finalize_templateIdsAligned_validated
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ id, id ∈ sourceLocalSchemeTemplateIds result.typedSource ↔
      id ∈ state.localSchemeAssumptions := by
  apply finalize_templateIdsAligned
    (aligned := fun id =>
      ((finalize_templateTracking success).classified_iff roots id).symm)
    success

/-- A template row in a successfully finalized source retains canonical
assumption evidence whenever the input state's executable classification is
aligned with the source-owned template identities. -/
theorem finalize_template_evidence
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (aligned : TemplateIdsAligned state roots)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ row, row ∈ result.solvedRequirements →
      row.id ∈ sourceLocalSchemeTemplateIds result.typedSource →
      row.evidence = .assumption row.predicate := by
  intro row member template
  have initialTemplate : row.id ∈ state.localSchemeAssumptions :=
    (finalize_templateIdsAligned aligned success row.id).mp template
  obtain ⟨patternState, finalState, requirements, _, _, _, _, patternResult,
      literalResult, _, _, _, _, requirementsResult, resultEq⟩ :=
    Detail.finalize_success_witness success
  have finalTemplate : row.id ∈ finalState.localSchemeAssumptions := by
    rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
      literalResult,
      Detail.defaultIntegerPatternTargets_localSchemeAssumptions
        patternResult]
    exact initialTemplate
  subst result
  exact solveRequirements_template_evidence requirementsResult row member
    finalTemplate

/-- Successful finalization alone supplies the ID alignment required to show
that every emitted qualified-template row retains assumption evidence. -/
theorem finalize_template_evidence_validated
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ row, row ∈ result.solvedRequirements →
      row.id ∈ sourceLocalSchemeTemplateIds result.typedSource →
      row.evidence = .assumption row.predicate := by
  apply finalize_template_evidence
    (aligned := fun id =>
      ((finalize_templateTracking success).classified_iff roots id).symm)
    success

/-- Proof-facing context for the requirement ledger emitted by finalization.
Both declaration assumptions and solved predicates use the final inference
substitution, while the complete solved ledger is retained for later lookup. -/
def finalizedRequirementContext
    (inferenceContext : Frontend.SourceInference.Context)
    (result : Frontend.SourceInference.Result) : SourceSemantics.Context :=
  ((SourceSemantics.Context.ofSignatures inferenceContext.signatures)
    |>.withAssumptions
      (inferenceContext.assumptions.map
        (TypedTraitResolution.applySubstitution result.substitution)))
    |>.withSolvedRequirements result.solvedRequirements

/-- Requirement-only semantic context projected from a checked function.  It
retains the final substitution on declaration predicates without yet adding
the declaration/type-variable fields used by deep body typing. -/
def checkedFinalizedRequirementContext
    (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature)
    (checked : CheckedFunction) : SourceSemantics.Context :=
  ((SourceSemantics.Context.ofSignatures signatures)
    |>.withAssumptions
      (signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution checked.substitution)))
    |>.withSolvedRequirements checked.solvedRequirements

/-- Successful finalization establishes the complete scoped requirement
ledger for its finalized source, including ordinary evidence and qualified
initializer-local assumption templates. -/
theorem finalize_scopedRequirementLedgerWellFormed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ScopedRequirementLedgerWellFormed
      (finalizedRequirementContext inferenceContext result)
      result.typedSource := by
  obtain ⟨patternState, finalState, solved, _, _, trackingValidation, _,
      patternDefault, literalDefault, _, _, ownershipValidation,
      scopeValidation, requirementsSolved, resultEq⟩ :=
    Detail.finalize_success_witness success
  have aligned := finalize_templateIdsAligned_validated success
  have templateOwnership := finalize_localSchemeTemplateOwnership success
  have ownershipFacts :=
    Detail.validateSourceRequirementOwnership_success ownershipValidation
  subst result
  have assumptionsEq : finalState.localSchemeAssumptions =
      state.localSchemeAssumptions := by
    rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
      literalDefault,
      Detail.defaultIntegerPatternTargets_localSchemeAssumptions
        patternDefault]
  have templateIff : ∀ requirement,
      requirement ∈ finalState.requirements →
      (requirement.id ∈ finalState.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds
          ((finalState.toTypedSource roots).applySubstitution
            finalState.inference.substitution)) := by
    intro requirement _
    rw [assumptionsEq]
    exact (aligned requirement.id).symm
  have templatesSubset :
      sourceLocalSchemeTemplateIds
          ((finalState.toTypedSource roots).applySubstitution
            finalState.inference.substitution) ⊆
        finalState.requirements.map (fun requirement => requirement.id) := by
    intro id templateMember
    have executableTemplateMember : id ∈
        ((finalState.toTypedSource roots).applySubstitution
          finalState.inference.substitution).localSchemeTemplateIds := by
      simpa using templateMember
    rw [typedSourceLocalSchemeTemplateIds_eq_sites] at executableTemplateMember
    rcases List.mem_map.mp executableTemplateMember with
      ⟨site, siteMember, siteIdEq⟩
    obtain ⟨requirement, _, requirementMember, requirementId, _, _, _, _⟩ :=
      Detail.validateSourceTemplateScopes_success scopeValidation site
        siteMember
    exact List.mem_map.mpr
      ⟨requirement, requirementMember, requirementId.trans siteIdEq⟩
  have templateScoped : ∀ requirement,
      requirement ∈ finalState.requirements →
      requirement.id ∈ finalState.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped
        ((finalState.toTypedSource roots).applySubstitution
          finalState.inference.substitution) {
          id := requirement.id
          predicate := Detail.applyPredicate finalState requirement.predicate
          evidence := .assumption
            (Detail.applyPredicate finalState requirement.predicate)
        } := by
    intro requirement requirementMember classified
    exact validateSourceTemplateScopes_success_rowScoped scopeValidation
      ownershipFacts.2.1 requirementMember
      ((templateIff requirement requirementMember).mp classified)
  let baseContext : SourceSemantics.Context :=
    (SourceSemantics.Context.ofSignatures inferenceContext.signatures)
      |>.withAssumptions
        (inferenceContext.assumptions.map
          (TypedTraitResolution.applySubstitution
            finalState.inference.substitution))
  have ledgerProof := solveRequirements_scoped_ledger_sound_of_nodup
    (baseContext := baseContext)
    ownershipFacts.2.1 (by rfl) (by rfl) templateOwnership templateIff
    templatesSubset templateScoped requirementsSolved
  simpa [finalizedRequirementContext, baseContext]
    using ledgerProof

/-- Exact executable source-to-ledger validation survives final substitution
and establishes the declarative whole-source requirement ownership judgment. -/
theorem finalize_requirementOwnership
    {semanticContext : SourceSemantics.Context}
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (solved_eq :
      semanticContext.solvedRequirements = result.solvedRequirements)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    RequirementOwnership semanticContext result.typedSource := by
  obtain ⟨_, finalState, solved, _, _, _, _, _, _, _, _,
      ownershipValidation, _, requirementsSolved, resultEq⟩ :=
    Detail.finalize_success_witness success
  have validated :=
    Detail.validateSourceRequirementOwnership_success ownershipValidation
  have idsEq := Detail.solveRequirements_preserves_ids inferenceContext
    finalState finalState.requirements solved requirementsSolved
  subst result
  constructor
  · simpa using validated.1
  · rw [solved_eq]
    simpa [idsEq] using validated.2.2

/-- Every successfully checked function body owns each solved requirement at
exactly one primary source occurrence, independently of ledger order. -/
theorem checkFunctionBody_success_requirementOwnership
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    RequirementOwnership (checkedBodyContext signatures signature checked)
      checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_requirementOwnership rfl finalizeSuccess

/-- Every successfully checked function body carries a complete scoped
requirement ledger in its final requirement-only semantic context. -/
theorem checkFunctionBody_success_scopedRequirementLedgerWellFormed
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ScopedRequirementLedgerWellFormed
      (checkedFinalizedRequirementContext signatures signature checked)
      checked.typedBody := by
  obtain ⟨_, _, _, result, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  simpa [checkedFinalizedRequirementContext, finalizedRequirementContext]
    using finalize_scopedRequirementLedgerWellFormed finalizeSuccess

/-- Executable finalization connects one retained integer-literal node to the
declarative validity judgment through its exact requirement row. -/
theorem finalize_integerLiteralValid_of_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (solvedValid :
      SolvedRequirementsValid
        (finalizedRequirementContext inferenceContext result)
        result.solvedRequirements)
    {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (member : Node.expression node ∈ state.nodes)
    (form_eq : node.form = .integerLiteral source resolution) :
    IntegerLiteralValid
      (finalizedRequirementContext inferenceContext result)
      source
      (resolution.applySubstitution result.substitution) := by
  obtain ⟨patternState, finalState, requirements, _, _, _, ledgerValidation,
      patternResult, literalResult, _, literalValidation, _,
      _, requirementsResult, resultEq⟩ :=
    Detail.finalize_success_witness success
  have ledger :=
    Detail.validateIntegerLiteralLedger_success_correspondence
      ledgerValidation
  obtain ⟨decoded, origin, originMember, _, targetEq, _, requirementMember⟩ :=
    ledger node source resolution member form_eq
  have finalOriginMember : origin ∈ finalState.integerLiterals := by
    rw [Detail.defaultIntegerLiteralTargets_integerLiterals literalResult,
      Detail.defaultIntegerPatternTargets_integerLiterals patternResult]
    exact originMember
  have supported :=
    Detail.validateIntegerLiteralTargets_success_supported literalValidation
      origin finalOriginMember
  have finalRequirementMember :
      ({ id := resolution.requirement, predicate := resolution.predicate } :
        Requirement) ∈ finalState.requirements := by
    rw [Detail.defaultIntegerLiteralTargets_requirements literalResult,
      Detail.defaultIntegerPatternTargets_requirements patternResult]
    exact requirementMember
  subst result
  refine integerLiteralValid_of_solved decoded ?_ finalRequirementMember
    requirementsResult rfl solvedValid
  simpa [targetEq, Frontend.SourceInference.State.resolve,
    TypeSystem.InferState.resolve] using supported

/-- When finalization starts without qualified-local templates, every emitted
solved row has independently valid retained evidence in the finalized
requirement context. -/
theorem finalize_solvedRequirementsValid
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (ordinary : state.localSchemeAssumptions = [])
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    SolvedRequirementsValid
      (finalizedRequirementContext inferenceContext result)
      result.solvedRequirements := by
  obtain ⟨patternState, finalState, requirements, _, _, _, _, patternResult,
      literalResult, _, _, _, _, requirementsResult, resultEq⟩ :=
    Detail.finalize_success_witness success
  have patternOrdinary : patternState.localSchemeAssumptions = [] := by
    rw [Detail.defaultIntegerPatternTargets_localSchemeAssumptions
      patternResult, ordinary]
  have finalOrdinary : finalState.localSchemeAssumptions = [] := by
    rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
      literalResult, patternOrdinary]
  subst result
  apply solveRequirements_ordinary_sound
    (inferenceContext := inferenceContext)
    (state := finalState)
    (requirements := finalState.requirements)
  · intro requirement member
    rw [finalOrdinary]
    simp
  · rfl
  · rfl
  · exact requirementsResult

/-- In an ordinary (non-template) source body, successful finalization alone
supplies the retained solver evidence needed for integer-literal validity. -/
theorem finalize_integerLiteralValid_of_mem_ordinary
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (ordinary : state.localSchemeAssumptions = [])
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (member : Node.expression node ∈ state.nodes)
    (form_eq : node.form = .integerLiteral source resolution) :
    IntegerLiteralValid
      (finalizedRequirementContext inferenceContext result)
      source
      (resolution.applySubstitution result.substitution) := by
  exact finalize_integerLiteralValid_of_mem success
    (finalize_solvedRequirementsValid ordinary success) member form_eq

end Solcore.SourceSemantics.SourceInferenceSoundness

namespace Solcore.SourceSemantics.FlexibleSubstitution

open Frontend SourceInference TypeSystem

/-- Once the inference pass has supplied a semantically valid closing
substitution, successful finalization transports the corresponding declarative
body derivation to the emitted typed source and result type. -/
theorem finalize_bodyHasType
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state : State} {roots : List NodeId} {result : Result}
    {sourceContext targetContext : SourceSemantics.Context}
    {closedVariables : List TypeVarId} {facts : BodyFacts}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : ContextSubstitutionValid result.substitution
      closedVariables sourceContext targetContext)
    (typing : BodyHasType (state.toTypedSource roots) sourceContext type facts) :
    BodyHasType result.typedSource targetContext result.type
      (applyBodyFacts result.substitution facts) := by
  rw [Detail.finalize_typedSource success, Detail.finalize_type success]
  exact BodyHasType.applySubstitution catalog contextValid typing

end Solcore.SourceSemantics.FlexibleSubstitution
