import Solcore.SourceSemantics.SourceCompiledPrivateBlockRestoration

/-! Actual scoped blocks pass the established active-variable invariants to
their child, then restore the genuine entering scope on the path to finalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_block (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {body : List Syntax.Statement} (form : source.value = .block body) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨bodyResult,bodyAccepted,completed,_⟩ := inferStatementFuel_success_block_facts form rfl accepted
    have expectedAtEntry := block.expectedBelow.weaken occurrence.before.next_le
    have properties := Detail.inferStatementsFuel_inferenceProperties occurrence.ready.allocateStatementId
      (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) expectedAtEntry bodyAccepted
    have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
      congrArg (fun result : Detail.StatementResult => result.state.inference) completed
    have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
      have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
      rw [same]
      exact List.prefix_append _ _
    have boundScope : occurrence.result.state.localBinders ⊆ bodyResult.state.localBinders := by
      have same := congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed
      rw [same]
      exact inferStatementsFuel_binders_subset (initial := occurrence.entry.allocateStatementId.2) bodyAccepted
    have reqs : occurrence.result.state.requirements = bodyResult.state.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
    refine ⟨{
      checkingFuel := childFuel, inferenceContext := block.inferenceContext, sources := body,
      expected := block.expected, entry := occurrence.entry.allocateStatementId.2, result := bodyResult,
      signatures := block.signatures, accepted := bodyAccepted, ready := occurrence.ready.allocateStatementId,
      nodesBelow := State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow,
      expectedBelow := expectedAtEntry,
      continuation := (State.InferenceProgress.of_inference_eq properties.2.1.solved unchanged).trans
        (occurrence.continuation.trans block.continuation),
      retained := nodes.trans (occurrence.retained.trans block.retained),
      entryWellFormed := occurrence.entryWellFormed,
      entryTemplates := occurrence.entryTemplates.congr rfl rfl rfl,
      entryOrigins := occurrence.entryOrigins.congr_localBinders rfl,
      entryPrivate := occurrence.entryPrivate.congr rfl rfl,
      entryBound := occurrence.entryBound,
      expectedClosed := block.expectedClosed,
      retainedSource := ?_,
      privacy := block.after_unchanged_occurrence occurrence unchanged boundScope reqs
    },rfl,rfl⟩
    refine ⟨?_,nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩
    exact block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
      (congrArg (fun result : Detail.StatementResult => result.state.owner) completed))

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
