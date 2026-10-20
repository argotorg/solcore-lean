import Solcore.Frontend.SourceInference.LocalGeneralizationInferenceReceipts

/-! A source statement at an actual position in an accepted block has its own
successful inference call and a semantic continuation to the block's returned
state. Both sides of the call are derived from the real sequence computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.StatementInferenceContinuation
open TypeSystem Detail

structure Occurrence (context : Context) (source : Syntax.Statement) (expected : Ty)
    (initial final : State) where
  fuel : Nat
  entry : State
  result : StatementResult
  accepted : inferStatementFuel fuel context source expected entry = .ok result
  ready : entry.InferenceReady
  before : initial.InferenceProgress entry
  continuation : result.state.InferenceProgress final
  retained : result.state.nodes <+: final.nodes

/-- The position refers to the original syntax list, including repeated
identical syntax. The witness is obtained by following that list's real calls. -/
theorem of_position_with_bounds {fuel : Nat} {context : Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (ready : initial.InferenceReady)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    ∃ occurrence : Occurrence context source expected initial result.state,
      occurrence.entry.NodesBelowNextOccurrence := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
      cases sources with
      | nil => simp at position
      | cons head rest =>
          cases headRun : inferStatementFuel fuel context head expected initial with
          | error error => simp [inferStatementsFuel, headRun, bind, Except.bind] at accepted
          | ok headResult =>
              have headProgress := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
              have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
              cases rest with
              | nil =>
                  have same : result.state = headResult.state := by
                    simp only [inferStatementsFuel, headRun, bind, Except.bind, pure, Pure.pure,
                      Except.pure, Except.ok.injEq] at accepted
                    exact (congrArg BlockResult.state accepted).symm
                  cases index with
                  | zero =>
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                      subst source
                      exact ⟨⟨fuel, initial, headResult, headRun, ready,
                        .refl ready.solved, same.symm ▸ State.InferenceProgress.refl headProgress.2.1.solved,
                        same.symm ▸ List.prefix_refl _⟩, nodesBelow⟩
                  | succ index => simp at position
              | cons next remaining =>
                  cases tailRun : inferStatementsFuel fuel context (next :: remaining) expected headResult.state with
                  | error error => simp [inferStatementsFuel, headRun, tailRun, bind, Except.bind] at accepted
                  | ok tailResult =>
                      have same : result.state = tailResult.state := by
                        simp only [inferStatementsFuel, headRun, tailRun, bind, Except.bind,
                          pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                        exact (congrArg BlockResult.state accepted).symm
                      have afterExpected := expectedBelow.weaken headProgress.1.next_le
                      cases index with
                      | zero =>
                          simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                          subst source
                          have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1
                            formation canonical afterExpected tailRun
                          exact ⟨⟨fuel, initial, headResult, headRun, ready, .refl ready.solved,
                            same.symm ▸ tailProgress.1, same.symm ▸
                              inferStatementsFuel_preserves_nodesPrefix tailRun (List.prefix_refl _) headBelow (Nat.le_refl _)⟩, nodesBelow⟩
                      | succ index =>
                          have restPosition : (next :: remaining)[index]? = some source := position
                          obtain ⟨found, foundBelow⟩ := ih headProgress.2.1 headBelow afterExpected tailRun restPosition
                          exact ⟨⟨found.fuel, found.entry, found.result, found.accepted, found.ready,
                            headProgress.1.trans found.before, same.symm ▸ found.continuation,
                            same.symm ▸ found.retained⟩, foundBelow⟩

theorem of_position {fuel : Nat} {context : Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (ready : initial.InferenceReady)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (Occurrence context source expected initial result.state) := by
  obtain ⟨occurrence, _⟩ := of_position_with_bounds ready nodesBelow formation canonical expectedBelow accepted position
  exact ⟨occurrence⟩

/-- An initialized declaration's actual child return reaches the whole block,
including every later statement. Annotation bounds come from source resolution. -/
theorem Occurrence.initialized {context : Context} {source : Syntax.Statement}
    {expected : Ty} {initial final : State}
    (occurrence : Occurrence context source expected initial final)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer))
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ∃ childFuel, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel context source occurrence.entry occurrence.result,
      receipt.ready.InferenceReady ∧ receipt.ready.InferenceProgress final := by
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, inferStatementFuel] at accepted
  | succ fuel =>
      rw [fuelEq] at accepted
      obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
      have inferred := receipt.initializer_inference occurrence.ready formation canonical
      exact ⟨fuel, receipt, inferred.2.1,
        (receipt.continuation inferred.2.1.solved).trans occurrence.continuation⟩

end Solcore.Frontend.SourceInference.StatementInferenceContinuation
