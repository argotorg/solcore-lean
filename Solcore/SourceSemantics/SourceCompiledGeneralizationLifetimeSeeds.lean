import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes
import Solcore.SourceSemantics.SourceCompiledInitializerReturnPrivacy
import Solcore.SourceSemantics.SourceInferenceGeneralizedInitializerState

/-! Every lifetime starts at a real initialized declaration, with the exact
binder and initializer retained by the same finalizer. No semantic typing or
continuation privacy premise is needed to produce this initial event. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

namespace BodyInitializerOccurrence
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

def lifetimeEvent (occurrence : BodyInitializerOccurrence selected source) :
    RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution
      occurrence.receipt.binding.1 occurrence.receipt.value.id where
  context := occurrence.inferenceContext
  entry := occurrence.entry
  readyState := occurrence.receipt.ready
  value := occurrence.receipt.value
  valueId := rfl
  computation := .statement occurrence.receipt
  ready := occurrence.ready
  extension := occurrence.extension
  retained := List.mem_flatMap.mpr ⟨_, occurrence.recorded, List.mem_singleton_self _⟩
  binderRetained := occurrence.retained

theorem lifetime
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected))
    (owner : occurrence.entry.owner = (evidenceSource selected).owner)
    (retained : occurrence.result.state.nodes <+: selected.body.returned.nodes) :
    GeneralizationLifetime occurrence.lifetimeEvent occurrence.entry.inference.next
      occurrence.result.state [occurrence.result.type] := by
  have extension : selected.body.finalized.substitution.SemanticallyExtends
      occurrence.result.state.inference.substitution := by
    simpa only [occurrence.receipt.inference_eq] using occurrence.extension
  have resultOwner : occurrence.result.state.owner = occurrence.entry.owner := by
    have accepted := initializedReceipt_accepted occurrence.receipt .unit
    exact Detail.inferStatementFuel_preserves_owner accepted
  have afterSource : TypingSourceExtends
      (occurrence.result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected) :=
    ⟨(resultOwner.trans owner).symm, retained⟩
  have after := operational.ofInitializer occurrence.receipt selected.body.resources ready
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    retained afterSource extension
  have member : occurrence.receipt.binding.1 ∈ occurrence.result.state.localBinders := by
    rw [occurrence.receipt.result_binders]
    exact List.mem_cons_self
  have resultType : occurrence.result.type = .unit :=
    congrArg Detail.StatementResult.type occurrence.receipt.completed
  have sameRequirements : occurrence.result.state.requirements = occurrence.receipt.ready.requirements :=
    congrArg (fun result : Detail.StatementResult => result.state.requirements) occurrence.receipt.completed
  refine {
    createdAfter := Nat.le_refl _
    allocated := occurrence.quantified_at_or_after_entry checked scope ready operational
    bound := after.quantifiersBelow _ member
    transport := SafeTransport.of_substitution_eq
      (congrArg InferState.substitution occurrence.receipt.inference_eq)
    live := after.privacy _ member
    values := ?_
    older := ?_
    newRows := ?_ }
  · intro type present
    cases List.mem_singleton.mp present
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  · intro type below
    have safe := occurrence.generalized_type_safe checked scope ready operational below
    simpa only [Safe, State.resolve, InferState.resolve, occurrence.receipt.inference_eq] using safe
  · intro requirement present fresh
    exact False.elim (fresh (sameRequirements ▸ present))

end BodyInitializerOccurrence
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
