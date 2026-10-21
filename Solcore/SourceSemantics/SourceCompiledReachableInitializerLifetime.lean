import Solcore.SourceSemantics.SourceCompiledActualGeneralizationLifetime
import Solcore.SourceSemantics.SourceCompiledGeneralizationLifetimeSeeds
import Solcore.SourceSemantics.SourceCompiledHeaderLifetimeSeeds

/-! The semantic boundary's exact initializer event is the one whose actual
call path supplies the completed lifetime. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open ProtectedVariables SourceCompiledGeneralizedSoundness SourceInferenceExecution
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized fuel}

theorem BodyInitializerOccurrence.actual_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {source : Syntax.Statement} (occurrence : BodyInitializerOccurrence selected source)
    {expectedReturn : Ty}
    (here : selected.InferenceCall (.statement (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result)) :
    GeneralizationLifetime occurrence.lifetimeEvent selected.inferenceCall.initial.inference.next
      selected.body.body.state [] := by
  have retained : ({binder := occurrence.receipt.binding.1, initializer := .expression occurrence.receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) :=
    List.mem_flatMap.mpr ⟨_, occurrence.recorded, List.mem_singleton_self _⟩
  obtain ⟨ready, extension, life⟩ := selected.statement_lifetime artifact checked position here occurrence.receipt retained
  exact life

theorem HeaderLifetime.actual_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (here : selected.InferenceCall (.forItem (childFuel + 1) context source initial result.1 result.2))
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial result)
    (ready : receipt.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders) :
    GeneralizationLifetime (HeaderLifetime.event receipt ready extension retained binderRetained)
      selected.inferenceCall.initial.inference.next selected.body.body.state [] := by
  obtain ⟨actualReady, actualExtension, life⟩ := selected.header_lifetime artifact checked position here receipt retained
  exact life

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
