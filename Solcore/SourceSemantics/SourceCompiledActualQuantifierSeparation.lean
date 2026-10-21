import Solcore.SourceSemantics.SourceCompiledActualGeneralizationSeparation
import Solcore.SourceSemantics.SourceInferenceActualCallOrderTraversal
import Solcore.SourceSemantics.SourceCompiledActualGeneralizationOrigins

/-! Every retained initialized owner comes from its actual inference call.
Comparing those paths derives quantifier separation for the complete body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open ProtectedVariables SourceCompiledGeneralizedSoundness SourceInferenceExecution
open ActualGeneralization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}

theorem BodySelection.initialized_quantifiers_disjoint
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {current : InitializedLetBinding}
    (member : current ∈ initializedLetBindings (evidenceSource selected)) :
    ∀ other ∈ initializedLetBindings (evidenceSource selected), other.binder ≠ current.binder →
      ∀ q ∈ current.binder.scheme.quantified, q ∉ other.binder.scheme.quantified := by
  obtain ⟨leftId, leftForm, leftOrigin⟩ := selected.actual_initialized_origin member
  obtain ⟨leftCall, leftHere, leftSite⟩ := leftOrigin.site
  have leftRetained : ({binder := current.binder, initializer := .expression leftId} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) := by
    simpa only [← leftForm] using member
  obtain ⟨leftEvent, leftSeed⟩ := leftSite.seed checked leftHere leftRetained
  intro other otherMember different
  obtain ⟨rightId, rightForm, rightOrigin⟩ := selected.actual_initialized_origin otherMember
  obtain ⟨rightCall, rightHere, rightSite⟩ := rightOrigin.site
  have rightRetained : ({binder := other.binder, initializer := .expression rightId} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) := by
    simpa only [← rightForm] using otherMember
  obtain ⟨rightEvent, rightSeed⟩ := rightSite.seed checked rightHere rightRetained
  exact Site.excludes_of_child_order artifact checked position
    (fun reached first second => ChildStep.ordered (selected.actualCall_inputs checked reached) first second)
    leftHere rightHere leftSite rightSite (fun same => different same.symm) leftSeed rightSeed

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
