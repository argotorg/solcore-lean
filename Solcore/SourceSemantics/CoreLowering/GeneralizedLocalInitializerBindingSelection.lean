import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBindingOrigins
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationResidualEntry
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBinderMetadata
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources

/-! The native binder and initializer selectors are tied to the same original
statement. Source ownership identifies a binder's initializer; the occurrence
forest identifies the binder of an initializer. Neither direction uses bundle size. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open CallableBodyMetadataViews

private theorem flatMap_sublist {α β : Type} (values : List α) (f g : α → List β)
    (each : ∀ value, List.Sublist (f value) (g value)) : List.Sublist (values.flatMap f) (values.flatMap g) := by
  induction values with
  | nil => exact .refl _
  | cons head rest ih => exact (each head).append ih

private theorem forItem_ids (item : ForItemForm) :
    List.Sublist ((forItemInitializedLetBindings item).map fun binding => binding.binder.id)
      (forItemDefinedLocalIds item) := by
  cases item <;> try exact .refl _
  rename_i binder initializer
  cases initializer <;> simp [forItemInitializedLetBindings, forItemDefinedLocalIds]

private theorem form_ids (form : StatementForm) :
    List.Sublist ((statementInitializedLetBindings form).map fun binding => binding.binder.id)
      (statementDefinedLocalIds form) := by
  cases form <;> try exact List.nil_sublist _
  case letDecl binder initializer =>
    cases initializer <;> simp [statementInitializedLetBindings, statementDefinedLocalIds]
  case forLoop initial condition post body =>
    simp only [statementInitializedLetBindings, statementDefinedLocalIds, List.map_append, List.map_flatMap]
    exact (flatMap_sublist initial _ _ forItem_ids).append (flatMap_sublist post _ _ forItem_ids)

private theorem initialized_ids (source : TypedSource) :
    List.Sublist ((initializedLetBindings source).map fun binding => binding.binder.id)
      (definedLocalIds source) := by
  unfold initializedLetBindings definedLocalIds
  rw [List.map_flatMap]
  apply List.sublist_append_of_sublist_right
  apply flatMap_sublist
  intro node
  cases node with
  | expression expression => exact List.nil_sublist _
  | statement statement => exact form_ids statement.form

private theorem same_binding {values : List InitializedLetBinding}
    (unique : (values.map fun binding => binding.binder.id).Nodup)
    {left right : InitializedLetBinding} (lm : left ∈ values) (rm : right ∈ values)
    (same : left.binder.id = right.binder.id) : left = right := by
  induction values with
  | nil => cases lm
  | cons head rest ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp lm with leftHead | leftTail
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact leftHead.trans rightHead.symm
      · exact False.elim (absent (List.mem_map.mpr
          ⟨right, rightTail, same.symm.trans (congrArg (fun binding => binding.binder.id) leftHead)⟩))
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact False.elim (absent (List.mem_map.mpr
          ⟨left, leftTail, same.trans (congrArg (fun binding => binding.binder.id) rightHead)⟩))
      · exact ih unique leftTail rightTail



private theorem initialized_statement {source : TypedSource} {statement : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : Node.statement statement ∈ source.nodes)
    (form : statement.form = .letDecl binder (some initializer)) :
    ({binder, initializer := .expression initializer} : InitializedLetBinding) ∈
      initializedLetBindings source := by
  apply List.mem_flatMap.mpr
  refine ⟨.statement statement, member, ?_⟩
  change _ ∈ statementInitializedLetBindings statement.form
  rw [form]
  exact List.mem_singleton_self _

private theorem exact_member {plan : SourceSpecializationWorklist.Plan} {caller : Key}
    {row actual : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan caller = .ok row)
    (member : actual ∈ plan.specializations) (owner : actual.key = caller) : actual = row := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  generalize filtered : plan.specializations.filter (fun entry => decide (entry.key = caller)) = entries at selected
  have picked : actual ∈ entries := by
    rw [← filtered]
    exact List.mem_filter.mpr ⟨member, by simpa using owner⟩
  cases entries with
  | nil => cases selected
  | cons head tail =>
    cases tail with
    | cons next rest => cases selected
    | nil => cases selected; exact List.mem_singleton.mp picked

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

private theorem binding_source (index : Index compiled bodyRelation)
    {binding : Binding}
    (origin : PreparedLocalBindingOrigins.BindingOrigin compiled.indexed.base.plan binding)
    (owner : binding.caller = index.owner) : binding.source = index.originalSource := by
  obtain ⟨original, selected, source⟩ := index.original_receipt
  obtain ⟨row, member, caller, sameSource, _⟩ := origin
  have same := exact_member selected member (caller.symm.trans owner)
  exact sameSource.trans (same ▸ source)

/-- This actual source identity includes bindings with an empty bundle. -/
theorem Index.native_binding_source (index : Index compiled bodyRelation)
    {binding : Binding} (member : binding ∈ compiled.indexed.base.locals.bindings)
    (owner : binding.caller = index.owner) : binding.source = index.originalSource :=
  binding_source index (SelectedCompilationBindingOrigins.of_compiled compiled binding member) owner

/-- The successful complete binder check and original identity ownership
identify the initializer used by the actual statement compiler. -/
theorem Index.lowerBinder_initializer (index : Index compiled bodyRelation)
    (ownership : LocalIdentityOwnership index.originalSource)
    {id : StatementId} {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : statement.form = .letDecl binder (some initializer))
    {scope : Scope} {type : Core.Ty}
    (accepted : lowerBinder compiled.indexed.base.locals index.owner index.active
      index.compilerSource scope binder = .ok type) :
    ∃ binding, compiled.indexed.base.locals.binding index.owner binder.id = .ok binding ∧
      binding.binder.applySubstitution index.active = binder ∧
      binding.initializer = initializer ∧ binding.source = index.originalSource ∧
      type = binding.bundleType index.active := by
  obtain ⟨binding, located, metadata, typeEq⟩ := lowerBinder_success accepted
  obtain ⟨origin, owner, _⟩ := SelectedCompilationBindingOrigins.at_binding compiled located
  have source := binding_source index origin owner
  obtain ⟨recorded, recordedMember, recordedForm⟩ := origin.statement
  rw [source] at recordedMember
  rw [index.compiler_original, lookupStatement_apply] at found
  obtain ⟨raw, rawFound, rfl⟩ := Option.map_eq_some_iff.mp found
  rcases raw with ⟨rawId, span, rawType, actual⟩
  cases actual <;> simp only [StatementNode.applySubstitution,
    StatementForm.applySubstitution] at form <;> try contradiction
  rename_i rawBinder rawInitializer
  obtain ⟨sameBinder, sameInitializer⟩ := StatementForm.letDecl.inj form
  cases sameInitializer
  have ids : binding.binder.id = rawBinder.id := by
    simpa only [TypedBinder.applySubstitution] using congrArg TypedBinder.id (metadata.trans sameBinder.symm)
  have actualMember := initialized_statement (lookupStatement?_sound rawFound).1 rfl
  have previousMember := initialized_statement recordedMember recordedForm
  have same := same_binding ((initialized_ids _).nodup ownership.unique)
    previousMember actualMember ids
  have initializers := congrArg InitializedLetBinding.initializer same
  exact ⟨binding, located, metadata, NodeId.expression.inj initializers, source, typeEq⟩

private theorem initialized_statement_edge {source : TypedSource} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : Node.statement node ∈ source.nodes)
    (form : node.form = .letDecl binder (some initializer)) :
    DirectChild source (.statement node.id) (.expression initializer) := by
  refine ⟨.statement node, ⟨member, rfl⟩, ?_⟩
  change _ ∈ node.form.references
  simp [form, StatementForm.references]

/-- The actual initializer search cannot choose another binder in the same
source forest. Its singleton catalog lookup then identifies the complete binding. -/
theorem Index.initializer_find_binding (index : Index compiled bodyRelation)
    (closed : OccurrenceGraphClosed index.originalSource)
    {binding : Binding} {binder : Resolved.LocalId}
    (located : compiled.indexed.base.locals.binding index.owner binder = .ok binding)
    {initial : Binding}
    (found : compiled.indexed.base.locals.bindings.find?
      (fun entry => decide (entry.caller = index.owner ∧ entry.initializer = binding.initializer)) =
        some initial) : initial = binding := by
  obtain ⟨origin, owner, binderId⟩ := SelectedCompilationBindingOrigins.at_binding compiled located
  have source := binding_source index origin owner
  have initialMember := List.mem_of_find?_eq_some found
  have picked : initial.caller = index.owner ∧ initial.initializer = binding.initializer := by
    simpa only [decide_eq_true_eq] using List.find?_some found
  have initialOrigin := SelectedCompilationBindingOrigins.of_compiled compiled initial initialMember
  have initialSource := binding_source index initialOrigin picked.1
  obtain ⟨left, leftMember, leftForm⟩ := initialOrigin.statement
  obtain ⟨right, rightMember, rightForm⟩ := origin.statement
  rw [initialSource] at leftMember
  rw [source] at rightMember
  have leftEdge := initialized_statement_edge leftMember leftForm
  rw [picked.2] at leftEdge
  have sameId := closed.childHasUniqueParent leftEdge (initialized_statement_edge rightMember rightForm)
  have sameStatement : left = right := by
    have leftLookup := lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique
      (show ContainsStatement index.originalSource left.id left from ⟨leftMember, rfl⟩)
    have rightLookup := lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique
      (show ContainsStatement index.originalSource right.id right from ⟨rightMember, rfl⟩)
    rw [NodeId.statement.inj sameId, rightLookup] at leftLookup
    exact (Option.some.inj leftLookup).symm
  rw [sameStatement, rightForm] at leftForm
  have sameBinder := (StatementForm.letDecl.inj leftForm).1.symm
  have actualId : initial.binder.id = binder := (congrArg TypedBinder.id sameBinder).trans binderId
  unfold Catalog.binding at located
  generalize filtered : compiled.indexed.base.locals.bindings.filter
    (fun entry => decide (entry.caller = index.owner ∧ entry.binder.id = binder)) = entries at located
  have matching : initial ∈ entries := by
    rw [← filtered]
    exact List.mem_filter.mpr ⟨initialMember, by simpa using And.intro picked.1 actualId⟩
  cases entries with
  | nil => cases located
  | cons head tail =>
    cases tail with
    | cons next rest => cases located
    | nil => cases located; exact List.mem_singleton.mp matching


private theorem exact_selected_member {plan : SourceSpecializationWorklist.Plan} {owner : Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next candidate only =>
    cases selected
    have member : row ∈ [row] := by simp
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases selected

/-- The source properties used by both selectors come from the actual cached
row's body finalizer and parameter specialization, for either invocation kind. -/
theorem Index.original_source_resources (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace fuel = .ok sourceCompiled.program) :
    OccurrenceGraphClosed index.originalSource ∧ LocalIdentityOwnership index.originalSource := by
  obtain ⟨row, rowFound, source⟩ := index.original_receipt
  obtain ⟨position, named, atPosition, sameRow⟩ :=
    SelectedCompilationCachedSources.row_position compiled (exact_selected_member rowFound)
  obtain ⟨selected, _⟩ := SourceBodyTemplateScope.cached_selection_scope artifact checked atPosition
  have graph : OccurrenceGraphClosed named.specialized.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
      named.specialized.parameterSubstitution selected.body.resources.graph_closed
  have ownership : LocalIdentityOwnership named.specialized.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.LocalIdentityOwnership.applyParameters
      named.specialized.parameterSubstitution selected.body.resources.local_identity_ownership
  rw [sameRow, source] at graph ownership
  exact ⟨graph, ownership⟩

private theorem binding_member {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} (located : catalog.binding caller binder = .ok binding) :
    binding ∈ catalog.bindings := by
  unfold Catalog.binding at located
  split at located
  · cases located
  · next actual only =>
    cases located
    have member : binding ∈ [binding] := by simp
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases located

/-- A real initialized statement and successful binder compilation force the
initializer search to return that same complete binding, including empty bundles.
Both uniqueness properties are supplied by the actual checked cached body. -/
theorem Index.initialized_binding_selected (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace fuel = .ok sourceCompiled.program)
    {id : StatementId} {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : statement.form = .letDecl binder (some initializer))
    {scope : Scope} {type : Core.Ty}
    (accepted : lowerBinder compiled.indexed.base.locals index.owner index.active
      index.compilerSource scope binder = .ok type) :
    ∃ binding, compiled.indexed.base.locals.binding index.owner binder.id = .ok binding ∧
      compiled.indexed.base.locals.bindings.find?
        (fun entry => decide (entry.caller = index.owner ∧ entry.initializer = initializer)) =
          some binding ∧
      binding.binder.applySubstitution index.active = binder ∧
      binding.initializer = initializer ∧ binding.source = index.originalSource ∧
      type = binding.bundleType index.active := by
  obtain ⟨graph, ownership⟩ := index.original_source_resources artifact checked
  obtain ⟨binding, located, metadata, initializerEq, source, typeEq⟩ :=
    index.lowerBinder_initializer ownership found form accepted
  have owner := (SelectedCompilationBindingOrigins.at_binding compiled located).2.1
  cases chosen : compiled.indexed.base.locals.bindings.find?
    (fun entry => decide (entry.caller = index.owner ∧ entry.initializer = initializer)) with
  | none =>
    have excluded := List.find?_eq_none.mp chosen binding (binding_member located)
    simp [owner, initializerEq] at excluded
  | some initial =>
    have same := index.initializer_find_binding graph located
      (show compiled.indexed.base.locals.bindings.find?
        (fun entry => decide (entry.caller = index.owner ∧ entry.initializer = binding.initializer)) =
          some initial from by simpa only [initializerEq] using chosen)
    exact ⟨binding, located, congrArg some same,
      metadata, initializerEq, source, typeEq⟩

/-- A reached initialized statement inside the current lambda cannot reuse
that lambda's own initializer. The actual finalized forest excludes the cycle. -/
theorem Index.initializer_ne_body_lambda (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace fuel = .ok sourceCompiled.program)
    {root : ExpressionId} {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty}
    (lambdaFound : index.compilerSource.lookupExpression? root = some lambda)
    (lambdaForm : lambda.form = .lambda parameters result index.statements)
    {id : StatementId} (reached : index.Reached (.statement id))
    {statement : StatementNode} (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : statement.form = .letDecl binder (some initializer)) : initializer ≠ root := by
  have originalGraph := (index.original_source_resources artifact checked).1
  have graph : OccurrenceGraphClosed index.compilerSource := by
    rw [index.compiler_original]
    exact FlexibleSubstitution.OccurrenceGraphClosed.applySubstitution index.active originalGraph
  have ancestry := CallableLambdaBodyReachability.Reaches.descends_from_lambda
    lambdaFound lambdaForm reached
  have contains := lookupStatement?_sound found
  have edge := initialized_statement_edge contains.1 form
  rw [contains.2] at edge
  intro same
  rw [same] at edge
  exact graph.acyclic _ (ancestry.trans (.direct edge))

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
