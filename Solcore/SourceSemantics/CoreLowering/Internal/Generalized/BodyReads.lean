import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ProgramCompletion
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.SelectedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies

/-!
# Generalized locals: reads

Reads of generalized locals in Source and in bodies: binding selection, inversion, scoped facts and admission.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerBindingSelection
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntryEffects
/-! Entering an actual materialized body writes only the unmapped context frame
and appends marked parameters. Both operations retain every generalized row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open GeneralizedLocalDescriptorOrigin

theorem Entry.scope_effect {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope captured.administrative viewRelation) (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    (registry : SourceCoreRawMetadata.Registry)
    (cells : GenericHeap.CellModel prepared.layouts.definitions)
    (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location)
    (callerNative : NativeFrame) (callerGhost : GhostFrame) (caller : MetadataState) (id : Word)
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id)
    (entry : Entry origin captured code inputs functions registry cells arguments nativeArguments before store
      location callerNative callerGhost caller id recipe)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions) :
    CellAwareScopeAuthority.Effect instances mapping world before store
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := by
  obtain ⟨suffix, extended⟩ := entry.entry.storeExtension
  rw [extended]
  exact (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode prepared.ancestry.layout.frame entry.next) entry.unmapped).trans
      (.append _ suffix entry.entry.metadata entry.entry.maps entry.entry.worlds)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedEntry
/-! The actual outer wrapper installs its read-time view, then the real marked
parameter prefix enters the selected lambda. The public caller remains the
saved physical row, even when it differs from the read-time context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionState
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  (material : Materialization compiled mapping world function) (view : View material)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (atFrame : view.location = owner.key.frameLocation)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "instances" => GeneralizedLocalInstanceValues.model compiled.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "temporaryStore" => store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame view.transient)

abbrev Entry := GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
  material.origin material.captured material.code inputs functions registry cells arguments nativeArguments before
  temporaryStore owner.key.frameLocation view.callerNative view.callerGhost view.caller view.id view.recipe

include atFrame in
/-- Actual view installation and parameter allocation construct the reached
owned state and descriptor-preserving effect, without a body execution premise. -/
theorem prepare
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world
      material.code.receipt.loweredParameters arguments nativeArguments)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller) :
    ∃ entry : Entry (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
      (before := before) (store := store) material view inputs functions owner,
    ∃ reached : State headers keys
      ⟨material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      Relates caller reached ∧ CallableIndexedOwnedIndirectExpressionHeads.StableRows reached ∧
      CellAwareScopeAuthority.Effect instances mapping world before store
        entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store ∧
      (∀ {value bodyStore}, Evaluates entry.entry.actualBody entry.entry.store
        (material.code.receipt.body.rename entry.entry.embedding) value bodyStore →
        Evaluates [view.native, DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload
          value (bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))) ∧
      (∀ {value finalStore}, Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore →
        ∃ bodyStore, Evaluates entry.entry.actualBody entry.entry.store
          (material.code.receipt.body.rename entry.entry.embedding) value bodyStore ∧
          finalStore = bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  let row := caller.rows owner.position
  have rowLocation : row.authority.frameLocation = owner.key.frameLocation := row.frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have absent := row.authority.unmapped
    simp only [rowLocation] at absent
    exact absent
  have reference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [← atFrame]
    exact view.lexicalReference
  have current : store.read? view.location = some
      (encode compiled.indexed.ancestry.layout.frame row.authority.current) := by
    rw [atFrame, ← rowLocation]
    exact row.authority.frame.read
  have reading := read_history view.carried view.recipe.read view.recipe.readAccepted
  let temporary := install caller owner.position reading
  have written : store.write? owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame view.transient) =
      some temporaryStore := Store.write?_eq_some_iff.mpr ⟨by
        have bound := (List.getElem?_eq_some_iff.mp current).1
        simpa only [atFrame] using bound, rfl⟩
  have referenceTyped : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    have typed := row.authority.typed
    simp only [rowLocation] at typed
    exact typed
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) referenceTyped
    (encode_runtime_typed world (CallableIndexedAmbient.frame_registered compiled.indexed) view.transient) written
  obtain ⟨entry, _added, _copied, _length, _spine, _slots, reached, related⟩ :=
    GeneralizedLocalOwnedBodyEntry.parameters_with_state material.origin material.captured material.code inputs functions
      GeneralizedLocalDescriptorHeap.ordinary_cells represented owner temporary view.carried view.recipe
      installedHeaps locals reference (Store.write?_reads_written written)
  have stableAway := GeneralizedLocalParameterAdmission.away_after_install caller owner.position stable reading
  have rows := GeneralizedLocalParameterAdmission.after_parameters temporary reached owner.position stableAway
    entry.nextHistory entry.entry.frame
  have effect := (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode compiled.indexed.ancestry.layout.frame view.transient) unmapped).trans
    (GeneralizedLocalBodyEntry.Entry.scope_effect (values := .initial compiled.compatible.checked)
      (prepared := compiled.indexed) material.origin material.captured material.code inputs
      functions registry cells arguments nativeArguments before temporaryStore owner.key.frameLocation
      view.callerNative view.callerGhost view.caller view.id view.recipe entry instances)
  have outer := GeneralizedLocalReadView.agreement view.reference current
    (parameter := material.code.receipt.parameterCore) (result := material.code.receipt.resultCore)
    (id := view.id) (target := material.code.descriptor.id) (caller := view.callerNative)
    (identity := .inLeft .word .unit)
    (innerBody := material.code.body.rename material.captured.embedding.lift.lift)
    (innerEnvironment := encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual)
    (argument := DataPatternValues.packValues nativeArguments)
  refine ⟨entry, reached, (install_related caller owner.position reading).trans related, rows, effect, ?_, ?_⟩
  · intro value bodyStore evaluated
    have inner := entry.wrap evaluated
    change Evaluates (DataPatternValues.packValues nativeArguments ::
      encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual)
      temporaryStore (material.code.body.rename material.captured.embedding.lift.lift) value
      (bodyStore.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame view.transient)) at inner
    rw [← atFrame] at inner
    have applied := outer.1 inner
    have full : Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value
        ((bodyStore.set view.location (encode compiled.indexed.ancestry.layout.frame view.transient)).set view.location
          (encode compiled.indexed.ancestry.layout.frame row.authority.current)) :=
      .apply (.second (.first (.var rfl))) (.var rfl) applied
    simpa only [List.set_set, atFrame] using full
  · intro value finalStore evaluated
    cases evaluated with
    | apply callee argument applied =>
      have expected : Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
          (.second (.first (.var 0)))
          (.closure material.code.receipt.parameterCore (LanguageResult.resultType material.code.receipt.resultCore)
            view.body (encode compiled.indexed.ancestry.layout.frame view.callerNative ::
              CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual :: view.environment))
          store := .second (.first (.var rfl))
      obtain ⟨sameClosure, sameStore⟩ := evaluation_deterministic callee expected
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj sameClosure
      rw [sameStore] at argument
      obtain ⟨sameArgument, sameAfter⟩ := evaluation_deterministic argument
        (show Evaluates [view.native, DataPatternValues.packValues nativeArguments] store (.var 1)
          (DataPatternValues.packValues nativeArguments) store from .var rfl)
      rw [sameArgument, sameAfter] at applied
      obtain ⟨innerStore, inner, restored⟩ := outer.2 applied
      rw [atFrame] at inner
      obtain ⟨bodyStore, body, innerEq⟩ := entry.unwrap inner
      refine ⟨bodyStore, body, ?_⟩
      simpa only [innerEq, atFrame, List.set_set] using restored

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
/-! The actual materialization identifies the original complete lambda body.
Its finite scanner receipt retains ordinary leaves and changing lexical scopes;
no caller supplies an execution law for that body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)

theorem view_source : material.code.view = function.source := material.view.trans material.source.symm

theorem lambda_fields : material.bodyProfile.parameters = function.parameters ∧
    material.bodyProfile.result = function.resultType ∧ material.bodyProfile.body = function.body := by
  have found := material.code.found
  rw [material.codeId, material.view] at found
  have same := Option.some.inj (material.bodyProfile.found.symm.trans found)
  have form := material.code.form.trans material.code.sourceForm
  exact ExpressionForm.lambda.inj (material.bodyProfile.form.symm.trans
    ((congrArg ExpressionNode.form same).trans form))

theorem scan : ScopedSourceBodyAdmission.Scan material.code.view
    (GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view)
    function.resultType true function.body := by
  obtain ⟨_,result,body⟩ := lambda_fields material
  rw [material.view]
  simpa only [result,body] using material.bodyProfile.scan

theorem lexical : CellAwareOrdinaryBodySyntax.lexicalOnly material.code.view
    (material.code.view.nodes.length + 1) function.body = true := by
  obtain ⟨_,_,body⟩ := lambda_fields material
  rw [material.view]
  simpa only [body] using material.bodyProfile.lexical

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerMeaning
/-! The actual finite initializer creates its ordered native closures in the
current lexical frame. It retains the complete Source descriptor without
executing the initializer or assuming any future instance body evaluation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerMeaning
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInitializerPackets (IndexedRows Receipt)

private theorem bundle_evaluates {actual : Core.Environment} {store : Store} {embedding : Renaming}
    {expressions : List Core.Expr} {values : List Value}
    (rows : ProductBundle.Pointwise (fun expression value =>
      Evaluates actual store (expression.rename embedding) value store) expressions values) :
    Evaluates actual store ((ProductBundle.expression expressions).rename embedding)
      (ProductBundle.value values) store := by
  induction rows with
  | nil => exact .unit
  | cons head tail ih =>
    cases tail with
    | nil => exact head
    | cons next rest => exact .pair head ih

/-- Every row is formed from its accepted compiler packet and the same actual
capture environment. The recorded lexical key is the initializer's key. -/
theorem rows_form {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    {candidates : List Instance} {expressions : List Core.Expr}
    (rows : IndexedRows prepared inputs lexical candidates expressions)
    (sources : ∀ candidate ∈ candidates, candidate.origin.source = binding.source)
    (binders : ∀ candidate ∈ candidates, candidate.origin.binder.id = binding.binder.id)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : ListRel (fun candidate raw => HasType
      (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type prepared.layouts.definitions) candidates expressions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    ∃ values,
      ProductBundle.Pointwise (fun expression value =>
        Evaluates actual store (expression.rename captured.embedding) value store) expressions values ∧
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Represents prepared mapping world
        function binding lexical) candidates values ∧
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Framed prepared mapping world
        function binding lexical location) candidates values := by
  induction rows with
  | nil => exact ⟨[], .nil, .nil, .nil⟩
  | @cons candidate raw rest remaining head tail ih =>
    cases typed with
    | cons rawTyped restTyped =>
      obtain ⟨packet, ⟨⟨indexed, sameLexical⟩, bodyProfile⟩⟩ := head
      have sameIndex : GeneralizedLocalInstanceValues.referenceIndex indexed =
          SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope := rfl
      obtain ⟨evaluated, framed⟩ := GeneralizedLocalInstanceValues.formation_at_frame indexed bodyProfile sameLexical
        owner initializer (sources candidate (by simp)) (binders candidate (by simp))
        descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer rawTyped stored (sameIndex ▸ reference) read
      obtain ⟨values, evaluations, representedRows, framedRows⟩ := ih (fun child member => sources child (List.mem_cons_of_mem _ member))
        (fun child member => binders child (List.mem_cons_of_mem _ member)) restTyped
      exact ⟨_, .cons evaluated evaluations, .cons framed.forget representedRows, .cons framed framedRows⟩

/-- The production initializer produces the complete bundle in the original
store. Its Source attachment retains the real binding and captured metadata. -/
theorem formation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalInstanceValues.model prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Represents prepared mapping world
        function binding lexical) (binding.atContext lexical) values ∧
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Framed prepared mapping world
        function binding lexical location) (binding.atContext lexical) values ∧
      GeneralizedLocalDescriptorHeap.Stored (GeneralizedLocalInstanceValues.model prepared)
        mapping world function (ProductBundle.value values) lowered.type := by
  obtain ⟨values, evaluations, rows, frames⟩ := rows_form receipt.rows receipt.sources receipt.binders descriptorSource owner initializer origin namedLexical namedMetadata captured declarations ownership issuer
    (receipt.raw_typed typed).2 stored reference read
  refine ⟨values, ?_, rows, frames, ?_⟩
  · rw [receipt.original.emitted]
    exact .inRight (bundle_evaluates evaluations)
  · have payload : lowered.type = binding.bundleType lexical :=
      congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted
    rw [payload]
    exact attachment.stored rows

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
/-! A reached generalized cell is materialized from original Source typing
and the actual caller dictionary. Static normalization does not replace the
original requirement spine or its descriptor's lexical context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
open Core Frontend SourceInference TypeSystem GeneralHeap

private theorem valid_at_binder {context : Context} {first second : TypedBinder}
    {type : TypeSystem.Ty} {requirements : List RequirementId}
    (scheme : first.scheme = second.scheme)
    (predicates : first.schemeRequirements = second.schemeRequirements)
    (valid : LocalSchemeInstantiationValid context first type requirements) :
    LocalSchemeInstantiationValid context second type requirements := by
  cases first with
  | mk firstId firstName firstScheme firstRequirements firstComptime firstSpan =>
    cases second with
    | mk secondId secondName secondScheme secondRequirements secondComptime secondSpan =>
      cases scheme
      cases predicates
      cases valid with
      | intro formation wellFormed substitution exact range result unique disjoint requirements =>
        refine .intro ⟨formation.ids_unique, ?_⟩ wellFormed substitution exact range result unique disjoint requirements
        intro requirement member
        have formed := formation.entries requirement member
        exact ⟨formed.predicate, formed.depends_on_quantified, formed.template⟩

/-- The genuine descriptor metadata identifies both its scheme and its
ordered principal requirements in the current lexical scope. -/
theorem instantiation_of_typed
    {source : TypedSource} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {location : Dynamic.Location}
    {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure} {compiled : Substitution}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType source context id node.type)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function)
    (principal : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements)
    (matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme node.rawType = some compiled)
    (covers : evidence.Covers context) :
    ∃ owned substitution produced,
      Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned ∧
      Dynamic.LocalSchemeRuntimeInstantiation context evidence function.binder node.rawType owned substitution produced := by
  generalize resultType : node.type = output at typed
  cases typed with
  | intro contains formTyped rawType _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at formTyped
    cases formTyped with
    | reference reference =>
      cases reference with
      | @«local» staticBinder raw owned schemeLookup requirementsLookup valid =>
        have identity := locals.lookup_generalized schemeLookup lookup read descriptor
        have principalEq := requirementsLookup.value_unique (identity.1 ▸ principal)
        have valid := valid_at_binder identity.2.symm principalEq valid
        have valid : LocalSchemeInstantiationValid context function.binder node.rawType _ := rawType ▸ valid
        obtain ⟨substitution, produced, runtime⟩ := GeneralizedLocalRuntimeInstantiation.of_valid matched valid covers
        cases requirements with
        | ordinary _ _ layout => exact ⟨_, substitution, produced, layout, runtime⟩

/-- This produces an actual staged Source step with the original requirement
identities. Its heap is unchanged because this admitted occurrence has no
output coercions. -/
theorem trace_of_typed
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : Context} {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {location : Dynamic.Location}
    {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure} {compiled : Substitution}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (typed : ExpressionHasType invocation.source context id node.type)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function)
    (fields : Dynamic.RuntimeContextFields function.definitionContext context)
    (principal : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements)
    (matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme node.rawType = some compiled)
    (covers : invocation.evidence.Covers context) :
    ∃ owned substitution produced size,
      Dynamic.LocalSchemeRuntimeInstantiation context invocation.evidence function.binder node.rawType owned substitution produced ∧
      Staging.Recursive.Size.Expression program registry size invocation context environment heap id
        (.value (.closure (function.instantiate substitution
          (produced ++ invocation.evidence.applySubstitution substitution)))) heap := by
  obtain ⟨owned, substitution, produced, layout, runtime⟩ :=
    instantiation_of_typed unique found form typed locals lookup read descriptor principal matched covers
  refine ⟨owned, substitution, produced, Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []], runtime, ?_⟩
  exact .generalizedLocal (lookupExpression?_sound found) form layout lookup read descriptor fields runtime
    (by rw [coercions]; exact .coercionsNil)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceReadInversion
/-! A genuinely retained generalized cell excludes ordinary reads at that
same location. Original requirement evidence closes the selected dictionary;
empty output coercions leave the source heap and materialized value intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
open Core Frontend SourceInference TypeSystem GeneralHeap

variable {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
  {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
  {size : Nat} {outcome : Staging.Recursive.Outcome}

theorem raw_type
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (coercions : node.coercions = [])
    (typed : ExpressionHasType invocation.source context id node.type) : node.rawType = node.type := by
  generalize result : node.type = type at typed
  cases typed with
  | intro contains _ raw _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    exact raw

theorem invert
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location cell) (descriptor : cell.generalized = some function)
    (requirementsUnique : RequirementIdsUnique context)
    (covers : invocation.evidence.Covers context)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id outcome after) :
    ∃ owned substitution produced,
      Dynamic.LocalSchemeRuntimeInstantiation context invocation.evidence function.binder node.rawType
        owned substitution produced ∧
      outcome = .value (.closure (function.instantiate substitution
        (produced ++ invocation.evidence.applySubstitution substitution))) ∧ after = before := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact otherRead.functional read
  have ordinary_false : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell.generalized = none → False := by
    intro otherLocation otherCell otherLookup otherRead empty
    cases same_cell otherLookup otherRead
    rw [descriptor] at empty
    cases empty
  cases outcome with
  | value value =>
    have plain := trace.sound.value_plain
    cases plain with
    | intro contains raw path =>
      cases same_node contains
      rw [form] at raw
      cases raw with
      | «local» _ otherLookup otherRead empty _
      | localEmptyMapping _ otherLookup otherRead empty _ _ _ =>
        exact False.elim (ordinary_false otherLookup otherRead empty)
    | generalizedLocal contains otherForm _ otherLookup otherRead otherDescriptor _ instantiation path =>
      cases same_node contains
      rw [form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      have sameFunction := Option.some.inj (otherDescriptor.symm.trans descriptor)
      cases sameFunction
      rw [coercions] at path
      cases path
      exact ⟨_, _, _, instantiation, rfl, rfl⟩
  | fault failure =>
    cases failure with
    | stage failedScope call reason =>
      exact False.elim (CellAwareSelectedReadBounds.no_stage unique found form coercions trace)
    | semantic reason =>
      have plain := trace.sound.semanticFault_plain
      cases plain with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
      | form contains raw =>
        cases same_node contains
        rw [form] at raw
        cases raw with
        | localUnbound _ unbound => exact False.elim (unbound.excludes_lookup lookup)
        | localDangling _ otherLookup dangling =>
          cases otherLookup.functional lookup
          exact False.elim (dangling.excludes_read read)
        | localUninitialized _ otherLookup otherRead empty _ _ =>
          exact False.elim (ordinary_false otherLookup otherRead empty)
      | coercion contains _ failed =>
        cases same_node contains
        rw [coercions] at failed
        cases failed
      | generalizedLocalRequirement _ _ _ _ _ _ _ selection failed =>
        obtain ⟨produced, producedOk⟩ := Dynamic.RequirementSequenceProves.produces_of_covers covers selection.requirements
        exact False.elim (producedOk.excludes_fault requirementsUnique failed)
      | generalizedLocalCoercion contains _ _ _ _ _ _ _ failed =>
        cases same_node contains
        rw [coercions] at failed
        cases failed

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopedReadFacts
/-! The exact original declaration identifies a polymorphic lexical scheme.
The actual environment and heap then force the descriptor branch; its stored
compiler binding and shared frame come from the physical scope authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopedReadFacts
open Core Frontend SourceInference TypeSystem GeneralHeap ReadOnly
open GeneralizedLocalLocatedRows

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {context : SourceSemantics.Context} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Core.Environment} {environment : Dynamic.Environment}

theorem binder
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt certificate) :
    certificate.read.binder = recipe.observations.binding.binder.id := by
  have original := Option.some.inj
    (certificate.observations.originalFound.symm.trans recipe.observations.originalFound)
  have normalized := Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
  obtain ⟨name, form⟩ := certificate.read.nodeForm
  rw [normalized, certificate.observations.form, original, recipe.observations.originalForm] at form
  exact ReferenceResolution.local.inj (ExpressionForm.reference.inj form).2.symm

structure Reached
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world heap store environment) where
  function : Dynamic.GeneralizedClosure
  location : Dynamic.Location
  lexical : Substitution
  located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) function certificate.read.binding lexical
    location mapping world heap store
  lookup : Dynamic.Environment.LooksUp environment certificate.read.binder location
  caller : named.signature.key = certificate.read.binding.caller
  binder : certificate.read.binder = certificate.read.binding.binder.id
  contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical []
  frames : located.Frames physical.location
  fields : Dynamic.RuntimeContextFields function.definitionContext context
  requirements : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements
  scheme : function.binder.scheme = certificate.read.binding.binder.scheme
  matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme certificate.observations.original.rawType =
    some certificate.read.child

theorem resolve
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt certificate)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world heap store environment)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment) : Nonempty (Reached certificate physical) := by
  have binderEq := binder certificate recipe
  have declared := physical.sourceDeclarations _ _ _ _
    (by simpa only [binderEq] using certificate.read.slot) recipe.observations.declaration
  obtain ⟨location, cell, lookup, read, _, storage⟩ := locals.lookup declared
  cases storage with
  | ordinary monomorphic _ => exact False.elim (recipe.observations.polymorphic monomorphic)
  | generalized descriptor sourceBinder sourceScheme =>
    obtain ⟨binding, lexical, located, caller, actualBinder, extension, frames, fields, requirements⟩ :=
      physical.generalized lookup read descriptor
    have bindingEq : certificate.read.binding = binding := by
      have registered : compiled.indexed.base.locals.binding named.signature.key certificate.read.binder = .ok binding := by
        simpa only [GeneralizedLocalInstanceValues.model, caller, actualBinder, binderEq] using located.attachment.registered
      exact Except.ok.inj (certificate.read.bindingFound.symm.trans registered)
    subst binding
    have matched := certificate.read.matched
    simp only [EmptySourceSubstitution.scheme, EmptySourceSubstitution.type] at matched
    have rawType := certificate.read.rawType
    simp only [EmptySourceSubstitution.type] at rawType
    have normalized := Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
    rw [rawType, normalized, certificate.observations.rawType] at matched
    refine ⟨⟨_, location, lexical, located, ?_, caller.symm, ?_, extension, frames, fields, requirements,
      sourceScheme.trans (congrArg (fun binding => binding.binder.scheme) recipe.binding), ?_⟩⟩
    · simpa only [binderEq] using lookup
    · exact binderEq.trans (congrArg (fun binding => binding.binder.id) recipe.binding)
    · simpa only [sourceScheme, recipe.binding] using matched

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopedReadFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionAdmission
/-! Actual closure typing, captured declarations and accepted compilation
supply the complete terminal expression certificate at the real parameter context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionAdmission
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  {expression : ExpressionId}
  (profile : GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view expression)
  (expressionSite : GeneralizedLocalBodyExpressionCertificate.Site material.inputs material.code.view expression)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  {program : Program} (frame : Dynamic.ClosureFrame program function)
  {invocation : Staging.Recursive.Scope} (source : invocation.source = function.source)
  (receipt : Receipt (GeneralizedLocalBodyCompiler.policy material) material.code.fuel material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    expression function.body material.code.receipt.resultCore material.code.reasonAt
    material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body)

include profile frame source in
theorem actual_tree :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (.initial compiled.compatible.checked)
      material.code.view inputs.context material.code.compilation.solvedRequirements material.code.reasonAt
      (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
      expression receipt.child ∧
    expressionSite.node.type = function.resultType ∧
    ExpressionHasType material.code.view inputs.context expression
      expressionSite.node.type := by
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters
    (values := .initial compiled.compatible.checked) material.code inputs frame material.capturedDeclarations
  have body := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended
  obtain ⟨finalContext, facts, bodyTyped, completes⟩ := body
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  have unique : NodeOccurrencesUnique invocation.source := source ▸ material.unique
  have head := receipt.head invocation (source.trans compilerSource.symm)
  rw [← source] at bodyTyped
  obtain ⟨node, found, type, typed⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped completes
  let site := expressionSite
  have foundView : material.code.view.lookupExpression? expression = some node := by
    rwa [source, ← compilerSource] at found
  have same := Option.some.inj (site.found.symm.trans foundView)
  have readTyped : ExpressionHasType material.code.view inputs.context expression site.node.type := by
    rw [source, ← compilerSource] at typed
    exact same.symm ▸ typed
  have accepted := receipt.generated
  rw [GeneralizedLocalBodyCompiler.expression_reader] at accepted
  change SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody
    (min receipt.childFuel material.code.fuel) material.code.compilation material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    expression material.code.reasonAt = .ok receipt.child at accepted
  refine ⟨GeneralizedLocalBodyExpressionCertificate.of_accepted material profile
    (by simpa only [compilerSource] using material.unique) (by simpa only [compilerSource] using declarations) site.found readTyped accepted, ?_, readTyped⟩
  exact (congrArg ExpressionNode.type same).trans type

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadAdmission
/-! Actual closure typing, captured declarations and accepted compilation
supply the complete terminal read certificate at the real parameter context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadAdmission
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  {expression : ExpressionId}
  (readSite : GeneralizedLocalBodyReadCertificate.Site material.inputs material.code.view expression)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  {program : Program} (frame : Dynamic.ClosureFrame program function)
  {invocation : Staging.Recursive.Scope} (source : invocation.source = function.source)
  (receipt : Receipt (GeneralizedLocalBodyCompiler.policy material) material.code.fuel material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    expression function.body material.code.receipt.resultCore material.code.reasonAt
    material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body)

include readSite frame source in
theorem actual_read :
    CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
      material.code.view inputs.context material.code.reasonAt
      (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
      expression receipt.child ∧
    readSite.node.type = function.resultType := by
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters
    (values := .initial compiled.compatible.checked) material.code inputs frame material.capturedDeclarations
  have body := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended
  obtain ⟨finalContext, facts, bodyTyped, completes⟩ := body
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  have unique : NodeOccurrencesUnique invocation.source := source ▸ material.unique
  have head := receipt.head invocation (source.trans compilerSource.symm)
  rw [← source] at bodyTyped
  obtain ⟨node, found, type, typed⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped completes
  let site := readSite
  have foundView : material.code.view.lookupExpression? expression = some node := by
    rwa [source, ← compilerSource] at found
  have same := Option.some.inj (site.found.symm.trans foundView)
  have readTyped : ExpressionHasType material.code.view inputs.context expression site.node.type := by
    rw [source, ← compilerSource] at typed
    exact same.symm ▸ typed
  have accepted := receipt.generated
  rw [GeneralizedLocalBodyCompiler.expression_reader] at accepted
  change SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody
    (min receipt.childFuel material.code.fuel) material.code.compilation material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    expression material.code.reasonAt = .ok receipt.child at accepted
  refine ⟨GeneralizedLocalBodyReadCertificate.lowered_read material site
    (by simpa only [compilerSource] using material.unique) (by simpa only [compilerSource] using declarations) readTyped accepted, ?_⟩
  exact (congrArg ExpressionNode.type same).trans type

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedHeapRead
/-! A genuine Source descriptor read recovers the actual allocation row from
the mixed heap relation. The binding and lexical context remain existential
until authentic allocation or capture provenance identifies the read caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
open Core Frontend SourceInference GeneralHeap GenericHeap
open GeneralizedLocalDescriptorHeap

variable {definitions : DataEnvironment} {catalog : SourceCoreDataCatalog.Catalog}
  {projects : GenericHeap.Projection} {ordinary : PayloadModel catalog projects definitions}
  {instances : InstanceModel definitions}

theorem of_heap_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (heaps : CellHeapRepresents (cellModel ordinary instances) mapping world heap store)
    (sourceRead : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function) :
    ∃ binding lexical, Nonempty (Located instances function binding lexical location mapping world heap store) := by
  obtain ⟨target, bundle, payload, reference, nativeRead, stored⟩ :=
    GeneralizedLocalDescriptorHeap.read heaps sourceRead descriptor
  cases stored with
  | bundle binding lexical registered captures origin binder initializer rows =>
    exact ⟨binding, lexical, ⟨⟨⟨registered, captures, origin, binder, initializer⟩,
      cell, sourceRead, descriptor, target, reference, _, rows, nativeRead⟩⟩⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows
end
