import Solcore.SourceSemantics.SourceInferenceActualCaptureRetention
import Solcore.SourceSemantics.SourceInferenceActiveQuantifierOrigins
import Solcore.SourceSemantics.SourceInferenceActiveHeaderPrivacy
import Solcore.Frontend.SourceInference.LocalGeneralizationInference

/-! Actual statement and header results expose every new polymorphic binder. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceInferenceSoundness.ProtectedVariables
namespace ActualCaptureOrigins

theorem statement_result
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult} {whole : TypedSource}
    (accepted : inferStatementFuel fuel context source expected initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : (result.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.state whole := by
  constructor
  intro binder member
  rcases inferStatementFuel_quantified_origin accepted binder member with old | mono | created
  · exact origins.origin binder old
  · exact .inl mono
  · obtain ⟨childFuel, receipt, rfl⟩ := created
    apply Or.inr
    apply retained
    exact List.mem_flatMap.mpr ⟨_, receipt.recorded, by
      simp [Node.initializedLetBinders, StatementForm.initializedLetBinders]⟩

theorem header_result
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State} {whole : TypedSource}
    (accepted : inferForItemFuel fuel context source initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : ∀ binding ∈ forItemInitializedLetBindings result.1,
      binding.binder ∈ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.2 whole := by
  constructor
  intro binder member
  rcases inferForItemFuel_quantified_origin accepted binder member with old | mono | created
  · exact origins.origin binder old
  · exact .inl mono
  · obtain ⟨childFuel, receipt, rfl⟩ := created
    apply Or.inr
    apply retained ⟨receipt.binding.1, .expression receipt.value.id⟩
    simp only [receipt.recorded, forItemInitializedLetBindings, List.mem_singleton]

theorem headers_result
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {whole : TypedSource}
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : ∀ binding ∈ result.items.flatMap forItemInitializedLetBindings,
      binding.binder ∈ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.state whole := by
  induction sources generalizing initial result with
  | nil =>
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact origins
  | cons source sources ih =>
    cases headAccepted : inferForItemFuel fuel context source initial with
    | error error => simp [inferForItemsFuel, headAccepted, bind, Except.bind] at accepted
    | ok head =>
      cases tailAccepted : inferForItemsFuel fuel context sources head.2 with
      | error error => simp [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
      | ok tail =>
        simp only [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind, pure,
          Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        have headOrigins := header_result headAccepted origins (fun binding member =>
          retained binding (List.mem_append_left _ member))
        exact ih (result := tail) tailAccepted headOrigins (fun binding member =>
          retained binding (List.mem_append_right _ member))

theorem statements_result
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {whole : TypedSource}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : (result.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.state whole := by
  induction fuel generalizing sources initial result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil =>
      simp only [inferStatementsFuel, Except.ok.injEq] at accepted
      cases accepted
      exact origins
    | cons source sources =>
      cases sources with
      | nil =>
        obtain ⟨head, headAccepted, same⟩ := inferStatementsFuel_success_singleton_facts accepted
        have headOrigins := statement_result headAccepted origins (by simpa only [same] using retained)
        simpa only [same] using headOrigins
      | cons next rest =>
        obtain ⟨head, tail, headAccepted, tailAccepted, same⟩ := inferStatementsFuel_success_cons_facts accepted
        have tailRetained : (tail.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders :=
          by simpa only [same] using retained
        have headRetained : (head.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders :=
          fun _ member => tailRetained ((LocalGeneralizationEvents.inferStatementsFuel_origins_progress tailAccepted).retained member)
        have headOrigins := statement_result headAccepted origins headRetained
        have tailOrigins := ih tailAccepted headOrigins tailRetained
        simpa only [same] using tailOrigins

end ActualCaptureOrigins
end Solcore.SourceSemantics.SourceInferenceExecution
