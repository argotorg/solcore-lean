import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledBlockContinuations
import Solcore.SourceSemantics.SourceCompiledInitializedPriorPrivacy
import Solcore.SourceSemantics.SourceInferenceLiveStatementPosition
import Solcore.SourceSemantics.SourceInferencePrivacyScopeRetention

/-! A reached block carries its actual prefix invariants and the privacy of
its real continuation. The selected check constructs the initial carrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

structure PrivateBlockContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) extends BlockContinuation selected where
  entryWellFormed : entry.RequirementsWellFormed
  entryTemplates : LiveTemplatesBacked entry
  entryOrigins : ActiveBinderCaptureOrigins entry
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  entryPrivate : ActiveQuantifiersPrivate entry
  entryBound : ActiveQuantifiersBelowNext entry
  expectedClosed : expected.VariablesBelow 0
  retainedSource : TypingSourceExtends
    (result.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  privacy : ∀ protectedVars,
    (∀ v ∈ protectedVars, v.index < result.state.inference.next) →
    LiveBindersSafe protectedVars result.state →
    SafeTransport protectedVars result.state selected.body.body.state ∧
      LiveBindersSafe protectedVars selected.body.body.state ∧
      ∀ requirement ∈ selected.body.body.state.requirements, requirement ∉ result.state.requirements →
        PredicateSafe protectedVars selected.body.body.state requirement.predicate

private theorem return_owner {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.owner = before.owner := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure] at accepted
    cases accepted
    rfl

namespace PrivateBlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

def of_selected (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) : PrivateBlockContinuation selected := by
  have monomorphic : ∀ entry ∈ (selected.signature.parameterNames.zip selected.signature.parameterTypes).map
      (fun parameter => (parameter.1,Scheme.mono parameter.2)), entry.2.quantified = [] := by
    intro entry member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    rfl
  have formation := Frontend.checkProgram_success_signature_formation checked
  refine {
    toBlockContinuation := BlockContinuation.of_selected selected checked
    entryWellFormed := State.initial_requirementsWellFormed _ _ _
    entryTemplates := LiveTemplatesBacked.initial _ _ _
    entryOrigins := activeBinderCaptureOrigins_initial_mono _ _ _ _ monomorphic
    entryPrivate := ActiveQuantifiersPrivate.initial _ _ _ monomorphic
    entryBound := activeQuantifiersBelowNext_initial_mono _ _ _ monomorphic
    expectedClosed := selected.returns_closed checked
    retainedSource := ?_
    privacy := ?_ }
  · refine ⟨return_owner selected.body.unified,?_⟩
    change selected.body.body.state.nodes <+: selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact List.prefix_rfl
  · intro protectedVars bound live
    exact ⟨.refl _ _,live,fun requirement member fresh => False.elim (fresh member)⟩

theorem position (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source) :
    Nonempty (LiveStatementPrivacyOccurrence block.inferenceContext source block.expected block.entry block.result.state
      selected.body.returned (selected.body.body.statements.map NodeId.statement)) := by
  have progress := selected.inferenceProgress checked
  exact liveStatementPrivacyOccurrence_of_position selected.body.resources block.ready block.entryWellFormed block.nodesBelow
    (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked)
    (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
    block.expectedBelow block.expectedClosed block.entryPrivate block.entryBound block.entryTemplates block.entryOrigins
    block.retainedSource (Substitution.SemanticallyExtends.trans progress.final_substitution block.continuation.substitution_extends)
    block.accepted position

end PrivateBlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
