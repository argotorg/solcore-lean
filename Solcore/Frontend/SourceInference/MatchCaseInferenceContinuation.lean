import Solcore.Frontend.SourceInference.StatementInferenceContinuation

/-! A match arm's actual body call retains the continuation through the later
arms and their lexical restoration. Positions refer to the original syntax. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.MatchCaseInferenceContinuation
open TypeSystem Detail

structure Occurrence (context : Context) (source : Syntax.MatchCase) (expected : Ty)
    (initial final : State) where
  fuel : Nat
  entry : State
  result : BlockResult
  accepted : inferStatementsFuel fuel context source.value.body.value expected entry = .ok result
  ready : entry.InferenceReady
  nodesBelow : entry.NodesBelowNextOccurrence
  expectedBelow : expected.VariablesBelow entry.inference.next
  before : initial.InferenceProgress entry
  continuation : result.state.InferenceProgress final
  retained : result.state.nodes <+: final.nodes

theorem of_position {fuel : Nat} {context : Context} {sources : List Syntax.MatchCase}
    {scrutinee expected : Ty} {initial : State} {result : MatchCasesResult}
    {index : Nat} {source : Syntax.MatchCase}
    (ready : initial.InferenceReady)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferMatchCasesFuel fuel context scrutinee expected initial.lexicalScope sources initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (Occurrence context source expected initial result.state) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferMatchCasesFuel] at accepted
  | succ fuel ih =>
      cases sources with
      | nil => simp at position
      | cons head rest =>
          unfold inferMatchCasesFuel at accepted
          simp only [bind, Except.bind] at accepted
          cases patternRun : inferMatchPatternFuel fuel context head.value.pattern scrutinee initial with
          | error error => simp [patternRun] at accepted
          | ok pair =>
              obtain ⟨pattern, patternState⟩ := pair
              simp only [patternRun] at accepted
              cases bodyRun : inferStatementsFuel fuel context head.value.body.value expected patternState with
              | error error => simp [bodyRun] at accepted
              | ok body =>
                  simp only [bodyRun] at accepted
                  cases tailRun : inferMatchCasesFuel fuel context scrutinee expected initial.lexicalScope rest
                      (body.state.restoreLexicalScope initial.lexicalScope) with
                  | error error => simp [tailRun] at accepted
                  | ok tail =>
                      simp only [tailRun, pure, Pure.pure, Except.pure] at accepted
                      injection accepted with same
                      subst result
                      have patternProperties := inferMatchPatternFuel_inferenceProperties ready scrutineeBelow formation patternRun
                      have patternBelow := (inferMatchPatternFuel_occurrenceBoundExtends patternRun).nodesBelowNextOccurrence nodesBelow
                      have expectedAtPattern := expectedBelow.weaken patternProperties.1.next_le
                      have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1
                        formation canonical expectedAtPattern bodyRun
                      have bodyBelow := (inferStatementsFuel_occurrenceBoundExtends bodyRun).nodesBelowNextOccurrence patternBelow
                      have restored := State.restoreLexicalScope_inferenceProperties ready
                        (patternProperties.1.trans bodyProperties.1)
                      have tailProperties := inferMatchCasesFuel_inferenceProperties restored.2 formation canonical
                        (scrutineeBelow.weaken restored.1.next_le) (expectedBelow.weaken restored.1.next_le) rfl tailRun
                      cases index with
                      | zero =>
                          simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                          subst source
                          exact ⟨⟨fuel, patternState, body, bodyRun, patternProperties.2.1,
                            patternBelow, expectedAtPattern, patternProperties.1,
                            (State.InferenceProgress.restoreLexicalScope body.state initial.lexicalScope
                              bodyProperties.2.1.solved).trans tailProperties.1,
                            inferMatchCasesFuel_preserves_nodesPrefix (result := tail) (state := body.state.restoreLexicalScope initial.lexicalScope) tailRun (List.prefix_refl _) bodyBelow (Nat.le_refl _)⟩⟩
                      | succ index =>
                          obtain ⟨found⟩ := ih restored.2 bodyBelow
                            (scrutineeBelow.weaken restored.1.next_le)
                            (expectedBelow.weaken restored.1.next_le) tailRun position
                          exact ⟨⟨found.fuel, found.entry, found.result, found.accepted, found.ready,
                            found.nodesBelow, found.expectedBelow, restored.1.trans found.before,
                            found.continuation, found.retained⟩⟩

end Solcore.Frontend.SourceInference.MatchCaseInferenceContinuation
