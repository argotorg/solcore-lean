import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission

/-! The saved descriptor and the actual emitted lambda discharge application
metadata checks. Read preparation remains a separate, occurrence-specific
ledger obligation; this proof does not assume a prepared application edge. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedReadApplication
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalAcceptedMaterialization
open SourceCoreCallableAncestryReadRecipes
open CallableAncestryMetadata (eraseRequirements eraseNodeRequirements)

private theorem erased_lookup (source : TypedSource) (id : ExpressionId) :
    (eraseRequirements source).lookupExpression? id =
      (source.lookupExpression? id).map (fun node => {node with requirements := []}) := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode?
  simp only [eraseRequirements, List.find?_map]
  have predicate : ((fun candidate : Node => decide (candidate.occurrenceId = id.occurrence)) ∘
      eraseNodeRequirements) = (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [predicate]
  cases found : source.nodes.find? (fun candidate => decide (candidate.occurrenceId = id.occurrence)) with
  | none => rfl
  | some node => cases node <;> rfl

private theorem pair_lambda
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {metadata : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame metadata source)
    {id : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    ∃ original : ExpressionNode, metadata.metadata.source.lookupExpression? id = some original ∧ original.form = node.form := by
  have same := congrArg (fun source : TypedSource => source.lookupExpression? id)
    (CallableAppliedDynamicSourceMaterialization.erase_source paired)
  rw [erased_lookup, erased_lookup, found] at same
  cases actual : metadata.metadata.source.lookupExpression? id with
  | none => simp [actual] at same
  | some original =>
    rw [actual] at same
    have erased : ({original with requirements := []} : ExpressionNode) = {node with requirements := []} :=
      Option.some.inj same
    have forms := congrArg ExpressionNode.form erased
    exact ⟨original, rfl, forms⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : GeneralHeap.LocationMap}
  {world : StoreTyping} {function : Dynamic.Closure}
  {viewRelation : TypedSource → TypedSource → Prop}

/-- The actual code selects the initializer and lexical owner checked by the
same real read. The header check follows from its real Source instantiation. -/
theorem apply_read (material : Materialization compiled mapping world function viewRelation)
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id : Word}
    (read : Read compiled.indexed.ancestry.graph.inputs caller id material.code.descriptor.id)
    (scheme : material.descriptor.binder.scheme = read.binder.scheme)
    (actualType : material.actualType = read.node.rawType) :
    material.descriptor.initializer = read.entry.view.principal.initializer ∧
    ∃ applied, applyRead read material.origin.metadata = .ok applied := by
  obtain ⟨template, selected, _authentic, owner, initial, _active, header⟩ :=
    CallableIndexedLambdaTemplatePermission.selected material.code
  have templateEq : read.template = template := Option.some.inj (read.targetSelected.symm.trans selected)
  have origins := SourceCoreStageCodebook.Origin.lambda.inj
    (read.templateOrigin.symm.trans read.viewOrigin)
  have initializer : material.descriptor.initializer = read.entry.view.principal.initializer := by
    calc
      material.descriptor.initializer = material.binding.initializer := material.descriptorInitializer
      _ = material.inputs.initializer := material.initializer.symm
      _ = material.code.id := material.codeId.symm
      _ = template.id := initial.symm
      _ = read.template.id := congrArg SourceCoreLambdaTemplates.Lambda.id templateEq.symm
      _ = read.entry.view.principal.initializer := origins.2.1
  have lexicalOwner : material.origin.metadata.metadata.owner = read.entry.view.owner := by
    calc
      material.origin.metadata.metadata.owner = material.binding.caller := material.origin.owner
      _ = material.inputs.current.owner := material.owner.symm
      _ = material.code.compilation.owner := by rw [material.compilation]; rfl
      _ = template.owner := owner.symm
      _ = read.template.owner := congrArg SourceCoreLambdaTemplates.Lambda.owner templateEq.symm
      _ = read.entry.view.owner := origins.1
  obtain ⟨node, member, form, _raw, _type, _requirements, _coercions⟩ := material.sourceCaptures.occurrence
  have found : material.descriptor.source.lookupExpression? material.descriptor.initializer = some node :=
    lookupExpression?_complete material.descriptorUnique member
  obtain ⟨original, originalFound, originalForm⟩ := pair_lambda material.origin.paired found
  rw [initializer] at originalFound
  have shape : original.form = .lambda material.descriptor.parameters material.descriptor.resultType
      material.descriptor.body := originalForm.trans form
  have instantiated : function = material.descriptor.instantiate read.substitution
      (material.produced ++ material.callerEvidence.applySubstitution material.semantic) :=
    material.materialized.trans (CallableAppliedRuntimeMaterialization.instantiated_closure_eq read
      material.descriptor material.instantiation scheme actualType)
  have nativeHeader : ExpressionForm.lambda
      (material.descriptor.parameters.map (TypedBinder.applySubstitution read.substitution))
      (read.substitution.apply material.descriptor.resultType) material.descriptor.body = read.template.node.form := by
    rw [instantiated] at header
    simpa only [Dynamic.GeneralizedClosure.instantiate, templateEq] using header.symm
  refine ⟨initializer, ?_⟩
  unfold applyRead
  split
  · split
    · next rejected => rw [originalFound] at rejected; cases rejected
    · next actual actualFound =>
      have same : actual = original := Option.some.inj (actualFound.symm.trans originalFound)
      subst actual
      split
      · next parameters resultType body actualShape =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.lambda.inj (actualShape.symm.trans shape)
        split
        · exact ⟨_, rfl⟩
        · contradiction
      all_goals rename_i rejected; exact False.elim (rejected _ _ _ shape)
  · contradiction

/-- Once the actual read factory succeeds, its saved lexical descriptor
produces the genuine paired-table edge. No application factory, edge coverage,
initializer equality or native-header condition is supplied by the caller. -/
theorem prepared_edge (material : Materialization compiled mapping world function viewRelation)
    {caller : SourceCoreCallableAncestryReadRecipes.State}
    {callerNative : CallableIndexedHistory.NativeFrame}
    {callerGhost : CallableIndexedHistory.GhostFrame} {id : Word}
    (carried : CallableIndexedHistory.Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table callerNative callerGhost (some caller))
    (read : Read compiled.indexed.ancestry.graph.inputs caller id material.code.descriptor.id)
    (accepted : prepareRead compiled.indexed.ancestry.graph.inputs caller id
      material.code.descriptor.id = .ok read)
    (scheme : material.descriptor.binder.scheme = read.binder.scheme)
    (actualType : material.actualType = read.node.rawType) :
    ∃ recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs
        callerGhost material.origin.ghost caller material.origin.metadata id material.code.descriptor.id,
      material.descriptor.initializer = recipe.read.entry.view.principal.initializer ∧
      recipe.read = read ∧
      ∃ callerIndex lexicalIndex destination,
        callerNative = .state (Int.ofNat callerIndex) ∧
        material.origin.native = .state (Int.ofNat lexicalIndex) ∧
        compiled.indexed.ancestry.graph.table.viewAt? callerIndex lexicalIndex id
          material.code.descriptor.id = some destination ∧
        compiled.indexed.ancestry.graph.table.stateAt? destination = some (read.after material.origin.metadata) := by
  obtain ⟨initializer, applied, application⟩ := apply_read material read scheme actualType
  let recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs
      callerGhost material.origin.ghost caller material.origin.metadata id material.code.descriptor.id :=
    ⟨carried.authenticates, material.origin.carried.authenticates, read, accepted, applied, application⟩
  obtain ⟨callerIndex, callerShape, callerStored⟩ := carried.state_shape
  obtain ⟨lexicalIndex, lexicalShape, lexicalStored⟩ := material.origin.carried.state_shape
  obtain ⟨destination, edge, stored⟩ :=
    (CallableAncestryPairedValidation.valid_closed compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.validated).view callerStored lexicalStored recipe.view_accepted
  exact ⟨recipe, initializer, rfl, callerIndex, lexicalIndex, destination,
    callerShape, lexicalShape, edge, stored⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedReadApplication
