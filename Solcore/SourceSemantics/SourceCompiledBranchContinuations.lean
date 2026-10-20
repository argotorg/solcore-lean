import Solcore.SourceSemantics.SourceCompiledBlockContinuations

/-! Branch calls share the actual condition state. Else inference starts from
the real restored then state, and both children retain the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BlockContinuation
open Frontend SourceInference TypeSystem
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : Selected compiled row fuel}

theorem enter_if_without_else (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {body : Syntax.Block} (form : source.value = .ifThen condition body none) :
    ∃ child : BlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, bodyResult, testAccepted, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_ifWithoutElse_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.formation checked) (block.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken
        testProperties.1.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := block.inferenceContext)
        testProperties.2.1 (block.formation checked) (block.canonical checked) expectedAtTest bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      refine ⟨{
        checkingFuel := childFuel,
        inferenceContext := block.inferenceContext,
        sources := body.value, expected := block.expected, entry := testState, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := testProperties.2.1,
        nodesBelow := ?_, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained)
      }, rfl, rfl⟩
      exact (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)

/-- Select either actual branch; both follow checker order and then inherit
the same outer continuation and finalizer. -/
theorem enter_if_with_else (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block}
    (form : source.value = .ifThen condition thenBody (some elseBody)) (isElse : Bool) :
    ∃ child : BlockContinuation selected,
      child.sources = (if isElse then elseBody else thenBody).value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, thenResult, elseResult, testAccepted, thenAccepted, elseAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_ifWithElse_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.formation checked) (block.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken testProperties.1.next_le
      have thenProperties := Detail.inferStatementsFuel_inferenceProperties testProperties.2.1
        (block.formation checked) (block.canonical checked) expectedAtTest thenAccepted
      have restored := State.restoreLexicalScope_inferenceProperties testProperties.2.1 thenProperties.1
      have expectedAtElse := expectedAtTest.weaken restored.1.next_le
      have elseProperties := Detail.inferStatementsFuel_inferenceProperties restored.2
        (block.formation checked) (block.canonical checked) expectedAtElse elseAccepted
      have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)
      have thenBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends thenAccepted).nodesBelowNextOccurrence testBelow
      have branchNodes : thenResult.state.nodes <+: elseResult.state.nodes :=
        Detail.inferStatementsFuel_preserves_nodesPrefix elseAccepted (List.prefix_refl _) thenBelow (Nat.le_refl _)
      have nodes : elseResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      have unchanged : occurrence.result.state.inference = elseResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have last := (State.InferenceProgress.of_inference_eq elseProperties.2.1.solved unchanged).trans
        (occurrence.continuation.trans block.continuation)
      have retained := nodes.trans (occurrence.retained.trans block.retained)
      cases isElse with
      | false =>
          exact ⟨{
            checkingFuel := childFuel, inferenceContext := block.inferenceContext,
            sources := thenBody.value, expected := block.expected, entry := testState, result := thenResult,
            signatures := block.signatures, accepted := thenAccepted, ready := testProperties.2.1,
            nodesBelow := testBelow, expectedBelow := expectedAtTest,
            continuation := (State.InferenceProgress.restoreLexicalScope thenResult.state
              testState.lexicalScope thenProperties.2.1.solved).trans (elseProperties.1.trans last),
            retained := branchNodes.trans retained
          }, rfl, rfl⟩
      | true =>
          exact ⟨{
            checkingFuel := childFuel, inferenceContext := block.inferenceContext,
            sources := elseBody.value, expected := block.expected,
            entry := thenResult.state.restoreLexicalScope testState.lexicalScope, result := elseResult,
            signatures := block.signatures, accepted := elseAccepted, ready := restored.2,
            nodesBelow := thenBelow, expectedBelow := expectedAtElse,
            continuation := last, retained := retained
          }, rfl, rfl⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BlockContinuation
