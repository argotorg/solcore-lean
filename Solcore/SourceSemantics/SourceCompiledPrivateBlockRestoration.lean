import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledPrivateBlockContinuation
import Solcore.SourceSemantics.SourceInferenceActiveScopePrivacy

/-! The actual statement suffix and containing block carry privacy after a
scoped child returns. Restoring binders consumes real child-scope membership. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem after_unchanged_occurrence (block : PrivateBlockContinuation selected)
    {source : Syntax.Statement}
    (occurrence : LiveStatementPrivacyOccurrence block.inferenceContext source block.expected block.entry block.result.state
      selected.body.returned (selected.body.body.statements.map NodeId.statement))
    {before : State}
    (inference : occurrence.result.state.inference = before.inference)
    (binders : occurrence.result.state.localBinders ⊆ before.localBinders)
    (requirements : occurrence.result.state.requirements = before.requirements) :
    ∀ protectedVars,
      (∀ v ∈ protectedVars, v.index < before.inference.next) →
      LiveBindersSafe protectedVars before →
      SafeTransport protectedVars before selected.body.body.state ∧
        LiveBindersSafe protectedVars selected.body.body.state ∧
        ∀ requirement ∈ selected.body.body.state.requirements, requirement ∉ before.requirements →
          PredicateSafe protectedVars selected.body.body.state requirement.predicate := by
  intro protectedVars bound live
  have boundAtStatement : ∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next := by
    simpa only [inference] using bound
  have same := SafeTransport.of_substitution_eq (protectedVars := protectedVars) (congrArg InferState.substitution inference)
  have liveAtStatement := live.restrict binders (congrArg InferState.substitution inference)
  have tail := occurrence.privacy protectedVars boundAtStatement liveAtStatement (safe_closed _ _ block.expectedClosed)
  have liveAtBlock := occurrence.liveAfter protectedVars boundAtStatement liveAtStatement (safe_closed _ _ block.expectedClosed)
  have boundAtBlock : ∀ v ∈ protectedVars, v.index < block.result.state.inference.next :=
    fun v member => Nat.lt_of_lt_of_le (boundAtStatement v member) occurrence.continuation.next_le
  have parent := block.privacy protectedVars boundAtBlock liveAtBlock
  refine ⟨same.trans (tail.1.trans parent.1),parent.2.1,?_⟩
  intro requirement member fresh
  by_cases inBlock : requirement ∈ block.result.state.requirements
  · have fromTail := tail.2 requirement inBlock (by simpa only [requirements] using fresh)
    intro type typeMember
    exact parent.1 type (fromTail type typeMember)
  · exact parent.2.2 requirement member inBlock

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
