import Solcore.SourceSemantics.SourcePreparedLocalReadTemplateExclusion
import Solcore.SourceSemantics.CoreLowering.SourceAuthenticatedReferenceOrigin
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources

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
