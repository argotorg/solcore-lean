import Solcore.SourceSemantics.SourceCompiledBranchContinuations
import Solcore.Frontend.SourceInference.MatchCaseInferenceContinuation
import Solcore.SourceSemantics.SourceInferenceStatementsSoundness

/-! Match bodies inherit the actual pattern state and all later arm/default
calls before the selected finalizer. No semantic body premise is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure CasesContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) where
  checkingFuel : Nat
  inferenceContext : SourceInference.Context
  sources : List Syntax.MatchCase
  scrutinee : Ty
  expected : Ty
  entry : State
  result : Detail.MatchCasesResult
  signatures : inferenceContext.signatures = compiled.program.signatures
  accepted : Detail.inferMatchCasesFuel checkingFuel inferenceContext scrutinee expected entry.lexicalScope sources entry = .ok result
  ready : entry.InferenceReady
  nodesBelow : entry.NodesBelowNextOccurrence
  scrutineeBelow : scrutinee.VariablesBelow entry.inference.next
  expectedBelow : expected.VariablesBelow entry.inference.next
  continuation : result.state.InferenceProgress selected.body.body.state
  retained : result.state.nodes <+: selected.body.body.state.nodes

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : Selected compiled row fuel}

theorem CasesContinuation.arm (cases : CasesContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.MatchCase} (position : cases.sources[index]? = some source) :
    ∃ child : BlockContinuation selected, child.sources = source.value.body.value ∧
      child.inferenceContext = cases.inferenceContext := by
  have formation : ProgramSignatureFormationValidated cases.inferenceContext.signatures :=
    cases.signatures.symm ▸ Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ cases.inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes) := by
    intro signature member
    rw [cases.signatures] at member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := MatchCaseInferenceContinuation.of_position cases.ready cases.nodesBelow
    formation canonical cases.scrutineeBelow cases.expectedBelow cases.accepted position
  exact ⟨{
    checkingFuel := occurrence.fuel, inferenceContext := cases.inferenceContext,
    sources := source.value.body.value, expected := cases.expected, entry := occurrence.entry,
    result := occurrence.result, signatures := cases.signatures, accepted := occurrence.accepted,
    ready := occurrence.ready, nodesBelow := occurrence.nodesBelow, expectedBelow := occurrence.expectedBelow,
    continuation := occurrence.continuation.trans cases.continuation,
    retained := occurrence.retained.trans cases.retained
  }, rfl, rfl⟩

namespace BlockContinuation

theorem match_without_default (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    (form : source.value = .matchWith scrutinees arms) (default : arms.value.defaultBody = none) :
    ∃ cases : CasesContinuation selected, cases.sources = arms.value.cases ∧
      cases.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨scrutinee, scrutineeState, hidden, hiddenState, cases, scrutineeRun,
        hiddenAllocation, casesRun, _, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_matchWithoutDefault_facts form default rfl accepted
      have properties := SourceInferenceSoundness.inferMatchScrutineesFuel_inferenceProperties
        occurrence.ready.allocateStatementId (block.formation checked) (block.canonical checked) scrutineeRun
      have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
      have hiddenReady : hiddenState.InferenceReady := hiddenEq ▸ properties.2.1.allocateHiddenLocal
      have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact properties.2.2
      have expectedBelow : block.expected.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact (block.expectedBelow.weaken occurrence.before.next_le).weaken properties.1.next_le
      have scrutineeNodes := SourceInferenceStatementsSoundness.inferMatchScrutineesFuel_success_nodesBelow
        scrutineeRun (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)
      have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
        rw [← hiddenEq]; exact scrutineeNodes
      have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady
        (block.formation checked) (block.canonical checked) scrutineeBelow expectedBelow rfl casesRun
      have unchanged : occurrence.result.state.inference = cases.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have retained : cases.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]; exact List.prefix_append _ _
      exact ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := arms.value.cases, scrutinee := scrutinee.type, expected := block.expected,
        entry := hiddenState, result := cases, signatures := block.signatures, accepted := casesRun,
        ready := hiddenReady, nodesBelow := hiddenNodes, scrutineeBelow := scrutineeBelow,
        expectedBelow := expectedBelow,
        continuation := (State.InferenceProgress.of_inference_eq casesProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := retained.trans (occurrence.retained.trans block.retained)
      }, rfl, rfl⟩

theorem match_with_default (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms} {body : Syntax.Block}
    (form : source.value = .matchWith scrutinees arms) (default : arms.value.defaultBody = some body) :
    ∃ cases : CasesContinuation selected, ∃ child : BlockContinuation selected,
      cases.sources = arms.value.cases ∧ cases.inferenceContext = block.inferenceContext ∧
      child.sources = body.value ∧ child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨scrutinee, scrutineeState, hidden, hiddenState, cases, defaultResult, scrutineeRun,
        hiddenAllocation, casesRun, defaultRun, _, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_matchWithDefault_facts form default rfl accepted
      have properties := SourceInferenceSoundness.inferMatchScrutineesFuel_inferenceProperties
        occurrence.ready.allocateStatementId (block.formation checked) (block.canonical checked) scrutineeRun
      have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
      have hiddenReady : hiddenState.InferenceReady := hiddenEq ▸ properties.2.1.allocateHiddenLocal
      have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact properties.2.2
      have expectedBelow : block.expected.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact (block.expectedBelow.weaken occurrence.before.next_le).weaken properties.1.next_le
      have scrutineeNodes := SourceInferenceStatementsSoundness.inferMatchScrutineesFuel_success_nodesBelow
        scrutineeRun (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)
      have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
        rw [← hiddenEq]; exact scrutineeNodes
      have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady
        (block.formation checked) (block.canonical checked) scrutineeBelow expectedBelow rfl casesRun
      have expectedAtDefault := expectedBelow.weaken casesProperties.1.next_le
      have defaultProperties := Detail.inferStatementsFuel_inferenceProperties casesProperties.2.1
        (block.formation checked) (block.canonical checked) expectedAtDefault defaultRun
      have casesNodes := (Detail.inferMatchCasesFuel_occurrenceBoundExtends casesRun).nodesBelowNextOccurrence hiddenNodes
      have toDefault : cases.state.nodes <+: defaultResult.state.nodes :=
        Detail.inferStatementsFuel_preserves_nodesPrefix defaultRun (List.prefix_refl _) casesNodes (Nat.le_refl _)
      have unchanged : occurrence.result.state.inference = defaultResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have retained : defaultResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]; exact List.prefix_append _ _
      have continuation := (State.InferenceProgress.of_inference_eq defaultProperties.2.1.solved unchanged).trans
        (occurrence.continuation.trans block.continuation)
      have nodeContinuation := retained.trans (occurrence.retained.trans block.retained)
      exact ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := arms.value.cases, scrutinee := scrutinee.type, expected := block.expected,
        entry := hiddenState, result := cases, signatures := block.signatures, accepted := casesRun,
        ready := hiddenReady, nodesBelow := hiddenNodes, scrutineeBelow := scrutineeBelow,
        expectedBelow := expectedBelow, continuation := defaultProperties.1.trans continuation,
        retained := toDefault.trans nodeContinuation
      }, {
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := body.value, expected := block.expected, entry := cases.state, result := defaultResult,
        signatures := block.signatures, accepted := defaultRun, ready := casesProperties.2.1,
        nodesBelow := casesNodes, expectedBelow := expectedAtDefault,
        continuation := continuation, retained := nodeContinuation
      }, rfl, rfl, rfl, rfl⟩

end BlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
