import Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedWorklist

/-!
Authentic paired ancestry retains the canonical source after erasing expression
requirement IDs. The actual named roots supply original specialization lookup;
the applied recipe keeps its rewritten source and cumulative semantic local
substitution. Native codebook contexts remain separate.

Both recursive selection constructors yield this correspondence. No full
substitution-only SourceReceipt, rewrite invariance, execution law or original
program typing is assumed or inferred.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open CallableAncestryMetadata

/-- The actual owned named seeds determine the original specialization for
any authenticated paired state, at arbitrary finite ancestry depth. -/
theorem authenticated_canonical
    {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame (some state)) :
    ∃ original,
      SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      eraseRequirements state.metadata.source =
        eraseRequirements (original.function.typedBody.applySubstitution state.metadata.active) := by
  have seeded := CallableAncestryPairedWorklist.named_roots_seeded inputs
  obtain ⟨root, member, valid⟩ :=
    CallableAncestryPairedValidation.authenticated_valid seeded
      (CallableAncestryPairedWorklist.named_roots_cover inputs) authenticated
  obtain ⟨original, selected, source, _sourceActive, _nativeActive⟩ := seeded root member
  refine ⟨original, ?_, ?_⟩
  · rw [valid.owner]
    exact selected
  · simpa only [source] using valid.canonical

/-- Exact descriptor origins and the lexical application owner identify the
same prepared sidecar. The source still contains all actual requirement rewrites. -/
theorem recipe_canonical
    {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
    {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
    {caller lexical : SourceCoreCallableAncestryReadRecipes.State}
    {view target : Core.Word}
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical view target)
    {sidecar : Sidecar}
    (prepared : prepareSidecar base.plan sidecar.caller.key = .ok sidecar)
    (sameOwner : recipe.read.template.owner = sidecar.caller.key) :
    eraseRequirements (recipe.read.after lexical).metadata.source =
      eraseRequirements (sidecar.source.applySubstitution
        (recipe.read.substitution.compose lexical.metadata.active)) := by
  obtain ⟨original, selected, canonical⟩ := authenticated_canonical recipe.authenticated
  have viewOwner : recipe.read.template.owner = recipe.read.entry.view.owner :=
    (SourceCoreStageCodebook.Origin.lambda.inj
      (recipe.read.templateOrigin.symm.trans recipe.read.viewOrigin)).1
  have owner : (recipe.read.after lexical).metadata.owner = sidecar.caller.key := by
    change lexical.metadata.owner = sidecar.caller.key
    exact recipe.applied.owner.trans (viewOwner.symm.trans sameOwner)
  rw [owner] at selected
  have same : original = sidecar.caller :=
    Except.ok.inj (selected.symm.trans (LambdaSourceAlignment.sidecar_lookup prepared))
  subst original
  simpa only [Sidecar.source, SourceCoreCallableAncestryReadRecipes.Read.after] using canonical

/-- Every actual recursive selection retains its full scope and exact semantic
substitution while exposing a canonical source correspondence after erasure. -/
theorem selected_canonical
    {program : CheckedProgram} {plan : Plan} {table : SourceCoreStageCodebook.Table}
    {function : Dynamic.Closure} {selected : Staging.Recursive.Scope}
    (related : RecursiveStageRegistry.Selected program plan table function selected) :
    ∃ sidecar active,
      prepareSidecar plan sidecar.caller.key = .ok sidecar ∧
      selected = RecursiveStageRegistry.scope sidecar active function ∧
      eraseRequirements function.source =
        eraseRequirements (sidecar.source.applySubstitution active) := by
  cases related with
  | lambda prepared _ source _ _ =>
      exact ⟨_, _, prepared, rfl, congrArg eraseRequirements (source.source prepared)⟩
  | applied recipe _ samePlan _ prepared sameOwner _ source _ _ =>
      refine ⟨_, _, prepared, rfl, ?_⟩
      rw [source]
      exact recipe_canonical recipe (by simpa only [samePlan] using prepared) sameOwner

end Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
