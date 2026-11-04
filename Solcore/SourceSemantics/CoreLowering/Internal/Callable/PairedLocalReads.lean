import Solcore.SourceSemantics.SourcePreparedLocalReadTemplateExclusion
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceStaging
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AncestryPaired
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AppliedViews
import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadTransport
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.Ancestry
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures

/-!
# Paired local reads

Transport, lookup and the qualified factory of paired local reads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLocalReadSourceTransport
/-! Local binder selection ignores requirement rewriting and commutes with
actual type substitution. These facts keep the real read factory connected
to its original template owner. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableLocalReadSourceTransport
open Frontend SourceInference TypeSystem SourceCoreCallableViews
open CallableAncestryMetadata CallableBodyMetadataViews
open CallableAncestryProfiles

private theorem lookup_erased (source : TypedSource) (id : ExpressionId) :
    (eraseRequirements source).lookupExpression? id =
      (source.lookupExpression? id).map (fun node => {node with requirements := []}) := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode?
  simp only [eraseRequirements, List.find?_map]
  have samePredicate : ((fun candidate : Node => decide (candidate.occurrenceId = id.occurrence)) ∘
        eraseNodeRequirements) = (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [samePredicate]
  cases source.nodes.find? (fun candidate => decide (candidate.occurrenceId = id.occurrence)) with
  | none => rfl
  | some node => cases node <;> rfl

private theorem lambda_erased (source : TypedSource) (id : ExpressionId) :
    SourceSpecialization.isDirectLambdaInitializer (eraseRequirements source) id =
      SourceSpecialization.isDirectLambdaInitializer source id := by
  unfold SourceSpecialization.isDirectLambdaInitializer
  rw [lookup_erased]
  cases source.lookupExpression? id with
  | none => rfl
  | some node => cases node with
    | mk id span type form requirements coercions localStart => cases form <;> rfl

private theorem lambda_apply (source : TypedSource) (substitution : Substitution) (id : ExpressionId) :
    SourceSpecialization.isDirectLambdaInitializer (source.applySubstitution substitution) id =
      SourceSpecialization.isDirectLambdaInitializer source id := by
  unfold SourceSpecialization.isDirectLambdaInitializer
  rw [lookupExpression_apply]
  cases source.lookupExpression? id with
  | none => rfl
  | some node => cases node with
    | mk id span type form requirements coercions localStart => cases form <;> rfl

/-- The exact first-match selector does not inspect expression requirements. -/
theorem binder_erased (source : TypedSource) (id : Resolved.LocalId) :
    SourceCompilationPlan.directLambdaLetBinder? (eraseRequirements source) id =
      SourceCompilationPlan.directLambdaLetBinder? source id := by
  unfold SourceCompilationPlan.directLambdaLetBinder?
  simp only [eraseRequirements, List.findSome?_map]
  congr 1
  funext node
  cases node with
  | expression node => rfl
  | statement node => cases node with
    | mk sid span type form =>
      cases form <;> try rfl
      next binder initializer =>
        cases initializer with
        | none => rfl
        | some initializer =>
          change (if binder.id != id || binder.scheme.quantified.isEmpty then none
            else if SourceSpecialization.isDirectLambdaInitializer (eraseRequirements source) initializer
              then some binder else none) = _
          simp only [lambda_erased]

/-- Substitution preserves the selector's ID, quantified-list, and lambda
checks, so it selects the same complete original binder. -/
theorem binder_apply (source : TypedSource) (substitution : Substitution) (id : Resolved.LocalId) :
    SourceCompilationPlan.directLambdaLetBinder? (source.applySubstitution substitution) id =
      (SourceCompilationPlan.directLambdaLetBinder? source id).map (TypedBinder.applySubstitution substitution) := by
  unfold SourceCompilationPlan.directLambdaLetBinder?
  simp only [TypedSource.applySubstitution, List.findSome?_map, List.map_findSome?]
  congr 1
  funext node
  cases node with
  | expression node => rfl
  | statement node => cases node with
    | mk sid span type form =>
      cases form <;> try rfl
      next binder initializer =>
        cases initializer with
        | none => rfl
        | some initializer =>
          change (if binder.id != id || binder.scheme.quantified.isEmpty then none
            else if SourceSpecialization.isDirectLambdaInitializer (source.applySubstitution substitution) initializer
              then some (binder.applySubstitution substitution) else none) =
            Option.map (TypedBinder.applySubstitution substitution)
              (if binder.id != id || binder.scheme.quantified.isEmpty then none
                else if SourceSpecialization.isDirectLambdaInitializer source initializer then some binder else none)
          simp only [lambda_apply]
          split <;> first | rfl | (split <;> rfl)

/-- The genuine paired derivation has one original selected source, even
when caller and lexical ancestry differ. Requirement IDs remain erased here. -/
theorem authenticated_original
    {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame (some state)) :
    ∃ original, SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      eraseRequirements state.metadata.source =
        eraseRequirements (original.function.typedBody.applySubstitution state.metadata.active) ∧
      CallableAncestrySourceActive.Reachable (CallableAncestrySourceActive.generators inputs.views)
        state.metadata.active := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named selected =>
    cases resultEq
    unfold SourceCoreCallableAncestryPairedPreparation.named? at selected
    obtain ⟨metadata, metadataSelected, rfl⟩ := Option.map_eq_some_iff.mp selected
    obtain ⟨original, found, sourceEq, empty⟩ :=
      CallableAncestryPairedProfiles.named_source inputs metadataSelected
    refine ⟨original, found, ?_, ?_⟩
    · change eraseRequirements metadata.source =
        eraseRequirements (original.function.typedBody.applySubstitution metadata.active)
      rw [sourceEq, empty, EmptySourceSubstitution.source]
    · change CallableAncestrySourceActive.Reachable _ metadata.active
      rw [empty]
      exact .empty
  | lambda ancestry allowed ih => exact ih resultEq
  | appliedView callerAncestry lexicalAncestry selected _callerIH lexicalIH =>
    cases resultEq
    obtain ⟨read, applied, _readAccepted, _appliedAccepted, same⟩ :=
      CallableAncestryPairedValidation.view_receipts selected
    rw [same]
    obtain ⟨original, found, canonical, reachable⟩ := lexicalIH rfl
    exact ⟨original, found,
      CallableAncestryReadRecipes.after_canonical read _ _
        (reachable.closed (CallableAncestrySourceActive.generators_valid inputs.views)) canonical,
      CallableAncestryReadRecipes.after_reachable read _ reachable⟩

private theorem exact_member {plan : SourceSpecializationWorklist.Plan}
    {key : SourceSpecialization.SpecializationKey} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i selected
  have present : row ∈ plan.specializations.filter (fun item => decide (item.key = key)) := by
    rw [selected]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp present).1

/-- Actual paired read witnesses cannot change any original local reference
of the same cached caller, after any source substitution. The owner selection
comes from the actual read's selector, without a separate first-match law. -/
theorem read_rewrite_unchanged
    {cached : SourceCoreUnifiedCompilation.Compiled}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs cached.indexed.base}
    {frame : SourceCoreCallablePairedFrames.Frame} {caller : SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame (some caller))
    {id target : Core.Word} (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
    {expression : ExpressionNode}
    (member : Node.expression expression ∈ read.specialized.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : expression.form = .reference name (.local localId))
    (substitution : Substitution) :
    SourceTypedRuntime.rewriteExpressionLocalRequirements read.witnesses
      (expression.applySubstitution substitution) = expression.applySubstitution substitution := by
  obtain ⟨original, originalSelected, canonical, _reachable⟩ := authenticated_original authenticated
  have same := Except.ok.inj (originalSelected.symm.trans read.specializedFound)
  subst original
  have detected := read.detected
  rw [← binder_erased caller.metadata.source, canonical, binder_erased, binder_apply] at detected
  obtain ⟨binder, selectedBinder, sameBinder⟩ := Option.map_eq_some_iff.mp detected
  obtain ⟨static, originalNode, originalName, staticSelected, staticSource, originalFound, _applied, originalForm⟩ :=
    SourceAuthenticatedReferenceOrigin.view_original_lookup read.entry.view
  have staticSelected : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan caller.metadata.owner =
      .ok static := by simpa only [read.owner] using staticSelected
  have same := Except.ok.inj (staticSelected.symm.trans read.specializedFound)
  subst static
  rw [← staticSource] at originalFound
  obtain ⟨index, named, position, namedEq⟩ :=
    SelectedCompilationCachedSources.row_position cached (exact_member read.specializedFound)
  have metadata := SourceCachedTemplateReceipts.cached_metadata cached position
  rw [namedEq] at metadata
  have factory := read.factory
  rw [← sameBinder] at factory
  exact SourcePreparedLocalReadTemplateExclusion.factory_read_unchanged metadata
    (lookupExpression?_sound originalFound).1 originalForm selectedBinder factory member form substitution

private theorem lookup_rewrite (source : TypedSource)
    (witnesses : List SourceTypedRuntime.LocalRequirementWitness) (id : ExpressionId) :
    (SourceTypedRuntime.rewriteLocalRequirements witnesses source).lookupExpression? id =
      (source.lookupExpression? id).map (SourceTypedRuntime.rewriteExpressionLocalRequirements witnesses) := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode?
  simp only [SourceTypedRuntime.rewriteLocalRequirements, List.find?_map]
  have samePredicate : ((fun candidate : Node => decide (candidate.occurrenceId = id.occurrence)) ∘
        (SourceTypedRuntime.rewriteNodeLocalRequirements witnesses)) =
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [samePredicate]
  cases source.nodes.find? (fun candidate => decide (candidate.occurrenceId = id.occurrence)) with
  | none => rfl
  | some node => cases node <;> rfl

/-- Every authentic ancestry step preserves the full local-reference lookup
apart from its recorded type substitution. Its requirements and coercions are
retained, rather than removed by an erasure relation. -/
theorem authenticated_local_lookup
    {cached : SourceCoreUnifiedCompilation.Compiled}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs cached.indexed.base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame (some state))
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan state.metadata.owner = .ok original)
    {id : ExpressionId} {expression : ExpressionNode}
    (found : original.function.typedBody.lookupExpression? id = some expression)
    {name : String} {localId : Resolved.LocalId}
    (form : expression.form = .reference name (.local localId)) :
    state.metadata.source.lookupExpression? id = some (expression.applySubstitution state.metadata.active) := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named named =>
    cases resultEq
    unfold SourceCoreCallableAncestryPairedPreparation.named? at named
    obtain ⟨metadata, metadataSelected, rfl⟩ := Option.map_eq_some_iff.mp named
    obtain ⟨row, rowSelected, sourceEq, empty⟩ :=
      CallableAncestryPairedProfiles.named_source inputs metadataSelected
    have same := Except.ok.inj (rowSelected.symm.trans selected)
    subst row
    change metadata.source.lookupExpression? id = some (expression.applySubstitution metadata.active)
    rw [sourceEq, empty, EmptySourceSubstitution.expression]
    exact found
  | lambda ancestry allowed ih => exact ih selected resultEq
  | @appliedView callerFrame lexicalFrame caller lexical result viewId target
      callerAncestry lexicalAncestry viewed _callerIH lexicalIH =>
    cases resultEq
    obtain ⟨read, applied, _readAccepted, _appliedAccepted, same⟩ :=
      CallableAncestryPairedValidation.view_receipts viewed
    rw [same] at selected ⊢
    have prior := lexicalIH (state := lexical) selected rfl
    obtain ⟨_row, _rowSelected, _canonical, reachable⟩ := authenticated_original lexicalAncestry
    have closed := reachable.closed (CallableAncestrySourceActive.generators_valid inputs.views)
    have readSelected : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan
        lexical.metadata.owner = .ok read.specialized := by
      rw [applied.owner, ← read.owner]
      exact read.specializedFound
    have rowEq := Except.ok.inj (readSelected.symm.trans selected)
    have unchanged := read_rewrite_unchanged callerAncestry read
      (rowEq.symm ▸ (lookupExpression?_sound found).1) form
      (read.substitution.compose lexical.metadata.active)
    change (SourceTypedRuntime.rewriteLocalRequirements read.witnesses
      (lexical.metadata.source.applySubstitution read.substitution)).lookupExpression? id = _
    rw [lookup_rewrite, lookupExpression_apply, prior]
    simp only [Option.map_some]
    rw [← SourceComposition.expression read.substitution lexical.metadata.active closed, unchanged]
    rfl

end Solcore.SourceSemantics.CoreLowering.CallableLocalReadSourceTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePairedLocalReadLookup
/-! Local-reference metadata agrees with the independently substituted Source
carried by the same actual paired history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedLocalReadLookup
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes
open CallableAncestryProfiles CallableBodyMetadataViews

/-- Each pair retains the successful preparation of that exact frame. -/
theorem authenticated
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    CallableAncestryPairedLookup.Authenticates inputs frame (some state) := by
  induction paired with
  | named selected => exact .named selected
  | lambda _prior allowed ih => exact .lambda ih allowed
  | applied _prior recipe _ih => exact recipe.authenticated

/-- The independent source of a real pair is exactly its original selected
caller under the source-active substitution recorded by that history. -/
theorem original_source
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    ∃ original, SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      source = original.function.typedBody.applySubstitution state.metadata.active := by
  induction paired with
  | named selected =>
    unfold SourceCoreCallableAncestryPairedPreparation.named? at selected
    obtain ⟨metadata, metadataSelected, rfl⟩ := Option.map_eq_some_iff.mp selected
    obtain ⟨original, found, same, empty⟩ := CallableAncestryPairedProfiles.named_source inputs metadataSelected
    refine ⟨original, found, ?_⟩
    change metadata.source = original.function.typedBody.applySubstitution metadata.active
    rw [same, empty, EmptySourceSubstitution.source]
  | lambda _prior _allowed ih => exact ih
  | @applied callerFrame lexicalFrame caller lexical source id target _prior recipe ih =>
    obtain ⟨original, found, same⟩ := ih
    obtain ⟨_row, _selected, _canonical, reachable⟩ :=
      CallableLocalReadSourceTransport.authenticated_original recipe.lexicalHistory
    refine ⟨original, found, ?_⟩
    change source.applySubstitution recipe.read.substitution =
      original.function.typedBody.applySubstitution (recipe.read.substitution.compose lexical.metadata.active)
    rw [same, SourceComposition.source recipe.read.substitution lexical.metadata.active
      (reachable.closed (CallableAncestrySourceActive.generators_valid inputs.views))]

/-- The actual runtime local read and the compiler metadata lookup are the
same complete record, including requirements and coercions. -/
theorem local_lookup
    {cached : SourceCoreUnifiedCompilation.Compiled} {inputs : Inputs cached.indexed.base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source)
    {id : ExpressionId} {expression : ExpressionNode}
    (found : source.lookupExpression? id = some expression)
    {name : String} {localId : Resolved.LocalId}
    (form : expression.form = .reference name (.local localId)) :
    state.metadata.source.lookupExpression? id = some expression := by
  obtain ⟨original, selected, sourceEq⟩ := original_source paired
  rw [sourceEq, lookupExpression_apply] at found
  obtain ⟨raw, rawFound, same⟩ := Option.map_eq_some_iff.mp found
  have rawForm : raw.form = .reference name (.local localId) := by
    have substituted := congrArg ExpressionNode.form same
    rw [form] at substituted
    cases shape : raw.form <;> simp [ExpressionNode.applySubstitution, shape,
      ExpressionForm.applySubstitution] at substituted
    rename_i rawName resolution
    cases resolution <;> simp_all [ReferenceResolution.applySubstitution]
  have actual := CallableLocalReadSourceTransport.authenticated_local_lookup (authenticated paired) selected rawFound rawForm
  rw [same] at actual
  exact actual

/-- The same pair also retains the exact first-match local binder selector.
Erasure changes only expression requirement lists, which this selector ignores. -/
theorem binder_lookup
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source)
    (id : Resolved.LocalId) :
    SourceCompilationPlan.directLambdaLetBinder? state.metadata.source id =
      SourceCompilationPlan.directLambdaLetBinder? source id := by
  rw [← CallableLocalReadSourceTransport.binder_erased state.metadata.source id,
    CallableAppliedDynamicSourceMaterialization.erase_source paired,
    CallableLocalReadSourceTransport.binder_erased source id]

end Solcore.SourceSemantics.CoreLowering.CallablePairedLocalReadLookup
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePairedQualifiedReadFactory
/-! The actual paired caller supplies the metadata lookup and original ledger
needed by prepareRead. Qualified factories come from executable preparation,
including every helper added to its completed frontier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedQualifiedReadFactory
open Frontend SourceInference TypeSystem
open CallableBodyMetadataViews
open SourcePreparedQualifiedLocalReadWitnesses SourcePreparedQualifiedLocalReadTransport

private theorem exact_member {plan : SourceSpecializationWorklist.Plan}
    {key : SourceSpecialization.SpecializationKey} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i selected
  have present : row ∈ plan.specializations.filter (fun item => decide (item.key = key)) := by
    rw [selected]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp present).1

/-- The cache's successful complete preparation retains witnesses for every
row, including rows absent from the caller's initial validation plan. -/
theorem cached_covered (cached : SourceCoreUnifiedCompilation.Compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (member : caller ∈ cached.indexed.base.plan.specializations) :
    Covered cached.sourceProgram caller := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  unfold SourceCompilationPlan.prepareExecutablePlanEvidence at prepared
  exact prepared_selected prepared member

/-- A real runtime local read has a successful metadata witness factory on the
same original specialization. No read-factory success, rewritten-source equality,
or source/native substitution equality is required from the consumer. -/
theorem paired_factory
    {cached : SourceCoreUnifiedCompilation.Compiled}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs cached.indexed.base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source)
    {id : ExpressionId} {expression : ExpressionNode}
    (found : source.lookupExpression? id = some expression)
    {name : String} {localId : Resolved.LocalId}
    (form : expression.form = .reference name (.local localId))
    {binder : TypedBinder}
    (detected : SourceCompilationPlan.directLambdaLetBinder? source localId = some binder)
    (qualified : binder.schemeRequirements ≠ []) :
    ∃ original available owned substitution witnesses,
      SourceCompilationPlan.exactSpecialization cached.indexed.base.plan state.metadata.owner = .ok original ∧
      SourceCompilationPlan.resolveRuntimeEvidenceEnvironment cached.indexed.base.sourceProgram
        original.key original.assumptions = .ok available ∧
      state.metadata.source.lookupExpression? id = some expression ∧
      SourceCompilationPlan.directLambdaLetBinder? state.metadata.source localId = some binder ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? expression = some owned ∧
      SourceCompilationPlan.localRequirementWitnesses original available binder
        {expression with type := expression.rawType, requirements := owned, coercions := []} =
          .ok (substitution, witnesses) := by
  obtain ⟨original, selected, sourceEq⟩ := CallablePairedLocalReadLookup.original_source paired
  have actualLookup := CallablePairedLocalReadLookup.local_lookup paired found form
  have actualBinder := (CallablePairedLocalReadLookup.binder_lookup paired localId).trans detected
  rw [sourceEq, lookupExpression_apply] at found
  obtain ⟨node, nodeFound, nodeEq⟩ := Option.map_eq_some_iff.mp found
  have rawForm : node.form = .reference name (.local localId) := by
    have substituted := congrArg ExpressionNode.form nodeEq
    rw [form] at substituted
    cases shape : node.form <;> simp [ExpressionNode.applySubstitution, shape,
      ExpressionForm.applySubstitution] at substituted
    rename_i rawName resolution
    cases resolution <;> simp_all [ReferenceResolution.applySubstitution]
  rw [sourceEq, CallableLocalReadSourceTransport.binder_apply] at detected
  obtain ⟨originalBinder, originalDetected, binderEq⟩ := Option.map_eq_some_iff.mp detected
  have originalQualified : originalBinder.schemeRequirements ≠ [] := by
    intro empty
    apply qualified
    rw [← binderEq]
    simp only [TypedBinder.applySubstitution, empty, List.map_nil]
  have member := exact_member selected
  obtain ⟨index, named, position, namedEq⟩ := SelectedCompilationCachedSources.row_position cached member
  have metadata := SourceCachedTemplateReceipts.cached_metadata cached position
  rw [namedEq] at metadata
  obtain ⟨available, owned, substitution, witnesses, resolved, ordinary, _binderFixed, _typeFixed, factory⟩ :=
    raw_of_preparation (cached_covered cached member) metadata
      (lookupExpression?_sound nodeFound).1 rawForm originalDetected originalQualified state.metadata.active
  have program := (SourceCoreUnifiedPreparationCertificates.compiled_fields cached).1
  rw [← program] at resolved
  rw [nodeEq] at ordinary factory
  rw [binderEq] at factory
  exact ⟨original, available, owned, substitution, witnesses, selected, resolved,
    actualLookup, actualBinder, ordinary, factory⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedQualifiedReadFactory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableViewReadSelection
/-! The static view and actual generalized local read use the same input node
and closed scheme matcher. Candidate identity follows from their real receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableViewReadSelection
open Frontend SourceInference TypeSystem SourceCoreCallableViews

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Actual view lowering checks one of the three authenticated forms of the
same expression. No completeness property of a source collector is used. -/
theorem lowered_node {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {table : Table program plan} {owner : Key} {active : Substitution} {source : TypedSource}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : SourceCoreCallableViewLowering.Viewed table owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt table owner active source id lowered = .ok receipt) :
    ∃ node, source.lookupExpression? id = some node ∧
      (node = receipt.entry.view.reference.original ∨
       node = receipt.entry.view.reference.normalized ∨ node = receipt.entry.view.rawRead) := by
  unfold SourceCoreCallableViewLowering.lowerWithReceipt at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · next selected selectedAt =>
    try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · split at accepted
      · cases accepted
      · next node actualFound =>
        try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
        split at accepted
        · next equal =>
          have forms : node = selected.view.reference.original ∨
              node = selected.view.reference.normalized ∨ node = selected.view.rawRead := by
            simpa [Bool.or_eq_true, or_assoc] using equal
          split at accepted
          · cases accepted
            exact ⟨node, actualFound, forms⟩
          · split at accepted
            · cases accepted
              exact ⟨node, actualFound, forms⟩
            · cases accepted
        · cases accepted
    · cases accepted

/-- All three accepted forms preserve the local resolution and uncoerced type. -/
theorem lowered_fields {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {table : Table program plan} {owner : Key} {active : Substitution} {source : TypedSource}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    {receipt : SourceCoreCallableViewLowering.Viewed table owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt table owner active source id lowered = .ok receipt)
    (found : source.lookupExpression? id = some node) :
    node.form = receipt.entry.view.reference.original.form ∧
      node.rawType = receipt.entry.view.rawRead.rawType := by
  obtain ⟨actual, lookup, forms⟩ := lowered_node accepted
  have equal := Option.some.inj (lookup.symm.trans found)
  subst actual
  rcases forms with rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem same_selection {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt ancestry.views owner active source id lowered = .ok receipt)
    (read : GeneralizedLocalReadReceipts.Certificate base.locals owner active source scope id reason lowered)
    (generalized : receipt.entry.view.wrapsPrincipal = true)
    (originalForm : ∃ name, receipt.entry.view.reference.original.form =
      .reference name (.local receipt.entry.view.binding.binder.id)) :
    receipt.entry.view.selectedInstance = some read.candidate ∧
      read.binding.source = receipt.entry.view.binding.source ∧
      read.binding.binder = receipt.entry.view.binding.binder ∧
      read.binding.initializer = receipt.entry.view.binding.initializer ∧
      read.child = receipt.entry.view.ownSubstitution := by
  obtain ⟨selection⟩ := CallablePreparedViewSelection.at_receipt ancestry receipt generalized
  have keys : receipt.entry.view.owner = owner ∧ receipt.entry.view.read = id ∧
      receipt.entry.view.parentActive = active := by
    simpa only [View.key, decide_eq_true_eq, Prod.mk.injEq] using List.find?_some receipt.found
  have fields := lowered_fields accepted read.nodeFound
  obtain ⟨name, form⟩ := originalForm
  obtain ⟨actualName, actualForm⟩ := read.nodeForm
  have binderId : read.binder = receipt.entry.view.binding.binder.id := by
    have eq := actualForm.symm.trans (fields.1.trans form)
    exact Option.some.inj (congrArg (fun form =>
      match form with | .reference _ (.local binder) => some binder | _ => none) eq)
  have located : base.locals.binding receipt.entry.view.owner receipt.entry.view.binding.binder.id =
      .ok read.binding := by simpa only [keys.1, ← binderId] using read.bindingFound
  have sameBinding : selection.binding = read.binding := Except.ok.inj (selection.located.symm.trans located)
  have binder : read.binding.binder = receipt.entry.view.binding.binder := by
    rw [← sameBinding]; exact selection.binder
  have staticMatch := CallableAncestryProfiles.SourceComposition.witnesses_matched receipt.entry.view.exactFactory
  simp only [TypedBinder.applySubstitution, Principal.binder, Scheme.apply, CallableAncestryProfiles.SourceComposition.mask_twice] at staticMatch
  change SourceSpecialization.matchClosedSchemeInstance?
    (Scheme.apply receipt.entry.view.parentActive receipt.entry.view.binding.binder.scheme)
    receipt.entry.view.rawRead.rawType = some receipt.entry.view.ownSubstitution at staticMatch
  have actualMatch := read.matched
  rw [read.rawType, fields.2, binder] at actualMatch
  simp only [keys.2.2] at staticMatch
  have child : read.child = receipt.entry.view.ownSubstitution := Option.some.inj (actualMatch.symm.trans staticMatch)
  have candidateMember : read.candidate ∈ selection.binding.instances := by
    rw [sameBinding]
    exact (List.mem_filter.mp (List.mem_of_getElem? read.candidate_at)).1
  have cumulative : read.candidate.origin.substitution = receipt.entry.view.cumulative := by
    have cumulativeExact := receipt.entry.view.cumulativeExact
    change receipt.entry.view.cumulative = receipt.entry.view.ownSubstitution.compose
      receipt.entry.view.parentActive at cumulativeExact
    simp only [keys.2.2] at cumulativeExact
    exact read.candidate_key.trans (by simpa only [child] using cumulativeExact.symm)
  have sameCandidate := selection.same_candidate candidateMember cumulative
  refine ⟨?_, ?_, binder, ?_, child⟩
  · exact selection.selected.trans (congrArg some sameCandidate.symm)
  · rw [← sameBinding]; exact selection.source
  · rw [← sameBinding]; exact selection.initializer

/-- The real lowerRead and lowerWithReceipt select the same complete candidate.
The original local resolution and both matcher keys come from successful
compiler checks, without a binding or substitution equality premise. -/
theorem same_read {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active id lowered}
    (accepted : SourceCoreCallableViewLowering.lowerWithReceipt ancestry.views owner active source id lowered = .ok receipt)
    (read : GeneralizedLocalReadReceipts.Certificate base.locals owner active source scope id reason lowered)
    (generalized : receipt.entry.view.wrapsPrincipal = true) :
    receipt.entry.view.selectedInstance = some read.candidate ∧
      read.binding.source = receipt.entry.view.binding.source ∧
      read.binding.binder = receipt.entry.view.binding.binder ∧
      read.binding.initializer = receipt.entry.view.binding.initializer ∧
      read.child = receipt.entry.view.ownSubstitution := by
  exact same_selection ancestry accepted read generalized
    (SourceAuthenticatedReferenceForm.original_form receipt.entry.view.authenticatedReference)

structure WrappedRead {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    (owner : Key) (active : Substitution) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (original lowered : SourceCoreBasic.LoweredExpr)
    (candidate : SourceCoreLocalPolymorphism.Instance) where
  receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active id original
  accepted : SourceCoreCallableViewLowering.lowerWithReceipt ancestry.views owner active source id original = .ok receipt
  generalized : receipt.entry.view.wrapsPrincipal = true
  selected : receipt.entry.view.selectedInstance = some candidate
  target : Core.Word
  origin : SourceCoreCallableIndexedAncestry.originId ancestry
    (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution) = .ok target
  parameter : Core.Ty
  result : Core.Ty
  carrier : original.type = .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word
  emitted : lowered = { original with expression :=
    (SourceCoreCallableIndexedAncestry.viewLower ancestry.layout.frame parameter result
      receipt.entry.id target (scope.length + 1 + base.globals.length) original.expression) }

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {result : α}
    (accepted : action.mapError f = .ok result) : action = .ok result := by
  cases action <;> cases accepted <;> rfl

/-- Actual indexed lowering either keeps the raw read or emits a wrapper for
exactly the complete candidate chosen by the same lowerRead certificate. -/
theorem lowerView_cases {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {original lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreCallableIndexedAncestry.lowerView ancestry owner active source scope id original = .ok lowered)
    (read : GeneralizedLocalReadReceipts.Certificate base.locals owner active source scope id reason original) :
    lowered = original ∨ Nonempty (WrappedRead ancestry owner active source scope id original lowered read.candidate) := by
  unfold SourceCoreCallableIndexedAncestry.lowerView at accepted
  obtain ⟨receipt, prepared, accepted⟩ := bind_ok accepted
  have actual := mapError_ok prepared
  split at accepted
  · cases accepted
    exact .inl rfl
  · next wrapped =>
    have generalized : receipt.entry.view.wrapsPrincipal = true := by simpa using wrapped
    have chosen := (same_read ancestry actual read generalized).1
    rw [chosen] at accepted
    dsimp only [bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨target, origin, accepted⟩ := bind_ok accepted
    split at accepted
    · next parameter result carrier =>
      cases accepted
      exact .inr ⟨⟨receipt, actual, generalized, chosen, target, origin, parameter, result, carrier, rfl⟩⟩
    · cases accepted

end Solcore.SourceSemantics.CoreLowering.CallableViewReadSelection
end
