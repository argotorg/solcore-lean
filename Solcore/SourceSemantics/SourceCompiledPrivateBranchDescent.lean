import Solcore.SourceSemantics.SourceCompiledPrivateConditionalDescent
import Solcore.SourceSemantics.SourceInferenceActiveBlockState

/-! Both branches follow the checker's actual order. Else starts after the
then scope is restored, and both continuations reach the same finalizer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_if_with_else (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block}
    (form : source.value = .ifThen condition thenBody (some elseBody)) (isElse : Bool) :
    ∃ child : PrivateBlockContinuation selected,
      child.sources = (if isElse then elseBody else thenBody).value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨test, testState, thenResult, elseResult, testAccepted, thenAccepted, elseAccepted, completed, _⟩ :=
      inferStatementFuel_success_ifWithElse_facts form rfl accepted
    have formation := block.toBlockContinuation.formation checked
    have canonical := block.toBlockContinuation.canonical checked
    have catalog : SignatureCatalogWellFormed block.inferenceContext.signatures :=
      block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
    have closed : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow 0 := by
      intro type member
      cases Option.some.inj member
      simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]
    have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
      formation canonical (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted
    have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken testProperties.1.next_le
    have thenProperties := Detail.inferStatementsFuel_inferenceProperties testProperties.2.1
      formation canonical expectedAtTest thenAccepted
    have restored := State.restoreLexicalScope_inferenceProperties testProperties.2.1 thenProperties.1
    have expectedAtElse := expectedAtTest.weaken restored.1.next_le
    have elseProperties := Detail.inferStatementsFuel_inferenceProperties restored.2
      formation canonical expectedAtElse elseAccepted
    have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
      (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
    have thenBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends thenAccepted).nodesBelowNextOccurrence testBelow
    have branchNodes : thenResult.state.nodes <+: elseResult.state.nodes :=
      Detail.inferStatementsFuel_preserves_nodesPrefix elseAccepted (List.prefix_refl _) thenBelow (Nat.le_refl _)
    have nodes : elseResult.state.nodes <+: occurrence.result.state.nodes := by
      rw [congrArg (fun result : Detail.StatementResult => result.state.nodes) completed]
      exact List.prefix_append _ _
    have unchanged : occurrence.result.state.inference = elseResult.state.inference :=
      congrArg (fun result : Detail.StatementResult => result.state.inference) completed
    have last := (State.InferenceProgress.of_inference_eq elseProperties.2.1.solved unchanged).trans
      (occurrence.continuation.trans block.continuation)
    have retained := nodes.trans (occurrence.retained.trans block.retained)
    have elseSource : TypingSourceExtends
        (elseResult.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) :=
      ⟨block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
        (congrArg (fun result : Detail.StatementResult => result.state.owner) completed)),
        nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩
    have thenSource : TypingSourceExtends
        (thenResult.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) :=
      (inferStatementsFuel_success_typingSourceExtends elseAccepted thenBelow _).trans elseSource
    have testWellFormed := (Detail.inferExprFuel_direct_progress testAccepted).wellFormed occurrence.entryWellFormed
    have testTemplates :=
      (show LiveTemplatesBacked occurrence.entry.allocateStatementId.2 from occurrence.entryTemplates.congr rfl rfl rfl).inferExprFuel
        occurrence.ready.allocateStatementId formation canonical
        (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted
    have testOrigins :=
      (occurrence.entryOrigins.congr_localBinders (final := occurrence.entry.allocateStatementId.2) rfl).inferExprFuel testAccepted
    have testPrivate :=
      (show ActiveQuantifiersPrivate occurrence.entry.allocateStatementId.2 from occurrence.entryPrivate.congr rfl rfl).inferExprFuel
        occurrence.ready.allocateStatementId occurrence.entryWellFormed occurrence.entryBound catalog formation canonical closed testAccepted
    have testBound := activeQuantifiersBelowNext_inferExprFuel (initial := occurrence.entry.allocateStatementId.2)
      occurrence.entryBound occurrence.ready.allocateStatementId formation canonical
      (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted
    have thenWellFormed := (Detail.inferStatementsFuel_direct_progress thenAccepted).wellFormed testWellFormed
    have thenExtension := Substitution.SemanticallyExtends.trans
      (selected.inferenceProgress checked).final_substitution
      (elseProperties.1.trans last).substitution_extends
    have thenActive := activeState_inferStatementsFuel selected.body.resources testProperties.2.1
      testWellFormed testBelow catalog formation canonical block.expectedClosed testPrivate testBound
      testTemplates testOrigins thenSource thenExtension thenAccepted
    have savedSubset : testState.localBinders ⊆ thenResult.state.localBinders :=
      inferStatementsFuel_binders_subset thenAccepted
    have elseSavedSubset : occurrence.result.state.localBinders ⊆ elseResult.state.localBinders := by
      rw [congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed]
      exact inferStatementsFuel_binders_subset
        (initial := thenResult.state.restoreLexicalScope testState.lexicalScope) elseAccepted
    have requirements : occurrence.result.state.requirements = elseResult.state.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
    have afterElse := block.after_unchanged_occurrence occurrence unchanged elseSavedSubset requirements
    cases isElse with
    | false =>
      refine ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := thenBody.value, expected := block.expected, entry := testState, result := thenResult,
        signatures := block.signatures, accepted := thenAccepted, ready := testProperties.2.1,
        nodesBelow := testBelow, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.restoreLexicalScope thenResult.state
          testState.lexicalScope thenProperties.2.1.solved).trans (elseProperties.1.trans last),
        retained := branchNodes.trans retained, entryWellFormed := testWellFormed,
        entryTemplates := testTemplates, entryOrigins := testOrigins, entryPrivate := testPrivate,
        entryBound := testBound, expectedClosed := block.expectedClosed, retainedSource := thenSource,
        privacy := ?_
      }, rfl, rfl⟩
      intro protectedVars bound live
      have restoredLive : LiveBindersSafe protectedVars
          (thenResult.state.restoreLexicalScope testState.lexicalScope) :=
        live.restrict savedSubset rfl
      have sibling := inferStatementsFuel_private protectedVars childFuel block.inferenceContext
        elseBody.value block.expected (thenResult.state.restoreLexicalScope testState.lexicalScope)
        restored.2 thenWellFormed bound restoredLive catalog formation canonical expectedAtElse
        (safe_closed _ _ block.expectedClosed) elseResult elseAccepted
      have outer := afterElse protectedVars
        (fun v member => Nat.lt_of_lt_of_le (bound v member) elseProperties.1.next_le) sibling.2.2.1
      exact ⟨sibling.1.trans outer.1, outer.2.1,
        new_requirements_trans sibling.2.2.2 outer.2.2 outer.1⟩
    | true =>
      exact ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := elseBody.value, expected := block.expected,
        entry := thenResult.state.restoreLexicalScope testState.lexicalScope, result := elseResult,
        signatures := block.signatures, accepted := elseAccepted, ready := restored.2,
        nodesBelow := thenBelow, expectedBelow := expectedAtElse,
        continuation := last, retained := retained, entryWellFormed := thenWellFormed,
        entryTemplates := testTemplates.transport (List.Subset.refl _)
          (Detail.inferStatementsFuel_requirements_subset thenAccepted) thenProperties.1.substitution_extends,
        entryOrigins := testOrigins.congr_localBinders rfl,
        entryPrivate := thenActive.1.restrict savedSubset rfl,
        entryBound := activeQuantifiersBelowNext_transport testBound rfl thenProperties.1.next_le,
        expectedClosed := block.expectedClosed, retainedSource := elseSource, privacy := afterElse
      }, rfl, rfl⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
