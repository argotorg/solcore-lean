import Solcore.Frontend.SourceInference.LocalGeneralizationInferenceReceipts

/-! Header positions retain their exact initializer call and continuation
through all later header items. The sequence is the executable for-item fold. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ForItemInferenceContinuation
open TypeSystem Detail

structure Occurrence (fuel : Nat) (context : Context) (source : Syntax.ForItem)
    (initial final : State) (forms : List ForItemForm) where
  entry : State
  result : ForItemForm × State
  accepted : inferForItemFuel fuel context source entry = .ok result
  ready : entry.InferenceReady
  before : initial.InferenceProgress entry
  continuation : result.2.InferenceProgress final
  retained : result.1 ∈ forms

theorem of_position {fuel : Nat} {context : Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {index : Nat} {source : Syntax.ForItem}
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (Occurrence fuel context source initial result.state result.items) := by
  induction sources generalizing initial result index with
  | nil => simp at position
  | cons head rest ih =>
      cases headRun : inferForItemFuel fuel context head initial with
      | error error => simp [inferForItemsFuel, headRun, bind, Except.bind] at accepted
      | ok pair =>
          rcases pair with ⟨headForm, headState⟩
          cases tailRun : inferForItemsFuel fuel context rest headState with
          | error error => simp [inferForItemsFuel, headRun, tailRun, bind, Except.bind] at accepted
          | ok tailResult =>
              have headProgress := inferForItemFuel_inferenceProperties ready formation canonical headRun
              have tailProgress := inferForItemsFuel_inferenceProperties headProgress.2 formation canonical tailRun
              have same : result = { items := headForm :: tailResult.items, state := tailResult.state } := by
                simp only [inferForItemsFuel, headRun, tailRun, bind, Except.bind,
                  pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                exact accepted.symm
              cases same
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                  subst source
                  exact ⟨⟨initial, (headForm, headState), headRun, ready,
                    .refl ready.solved, tailProgress.1, List.mem_cons_self⟩⟩
              | succ index =>
                  obtain ⟨found⟩ := ih headProgress.2 tailRun position
                  exact ⟨⟨found.entry, found.result, found.accepted, found.ready,
                    headProgress.1.trans found.before, found.continuation,
                    List.mem_cons_of_mem _ found.retained⟩⟩

theorem Occurrence.initialized {fuel : Nat} {context : Context} {source : Syntax.ForItem}
    {initial final : State} {forms : List ForItemForm}
    (occurrence : Occurrence fuel context source initial final forms)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer))
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ∃ childFuel, ∃ receipt : LocalHeaderRequirementTiming.Receipt childFuel context source occurrence.entry occurrence.result,
      receipt.ready.InferenceReady ∧ receipt.ready.InferenceProgress final ∧
        .letDecl receipt.binding.1 (some receipt.value.id) ∈ forms := by
  have accepted := occurrence.accepted
  cases fuel with
  | zero => simp [inferForItemFuel] at accepted
  | succ fuel =>
      obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_initialized_accepted form accepted
      have inferred := receipt.initializer_inference occurrence.ready formation canonical
      exact ⟨fuel, receipt, inferred.2.1,
        (receipt.continuation inferred.2.1.solved).trans occurrence.continuation,
        receipt.recorded ▸ occurrence.retained⟩

end Solcore.Frontend.SourceInference.ForItemInferenceContinuation
