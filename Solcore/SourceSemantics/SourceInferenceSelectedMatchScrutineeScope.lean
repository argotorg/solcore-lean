import Solcore.SourceSemantics.SourceInferenceSoundness

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference

/-- Actual match scrutinee inference preserves the caller's lexical scope,
including the allocation and recording of a generated tuple. -/
theorem inferMatchScrutineesFuel_success_lexicalScope_eq
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial : State} {result : InferredExpression × State}
    (success : inferMatchScrutineesFuel fuel context span sources initial = .ok result) :
    result.2.lexicalScope = initial.lexicalScope := by
  have generated {elements : List InferredExpression} {elementsState : State}
      (accepted : Detail.inferExprsFuel fuel context sources initial = .ok (elements, elementsState))
      (recorded : result =
        (⟨elementsState.allocateExpressionId.1, TypeSystem.Ty.productMany (elements.map (·.type))⟩,
          elementsState.allocateExpressionId.2.recordNode (.expression {
            id := elementsState.allocateExpressionId.1, span,
            type := TypeSystem.Ty.productMany (elements.map (·.type)),
            form := .tuple (elements.map (·.id)) }))) :
      result.2.lexicalScope = initial.lexicalScope := by
    rw [recorded]
    exact Detail.inferExprsFuel_success_lexicalScope_eq accepted
  cases sources with
  | nil =>
    unfold inferMatchScrutineesFuel at success
    cases accepted : Detail.inferExprsFuel fuel context [] initial with
    | error error => simp [accepted, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨elements, elementsState⟩ := pair
      simp only [accepted, bind, Except.bind] at success
      exact generated accepted (Except.ok.inj success).symm
  | cons first rest =>
    cases rest with
    | nil =>
      exact Detail.inferExprFuel_success_lexicalScope_eq (by
        simpa [inferMatchScrutineesFuel] using success)
    | cons second rest =>
      unfold inferMatchScrutineesFuel at success
      cases accepted : Detail.inferExprsFuel fuel context (first :: second :: rest) initial with
      | error error => simp [accepted, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨elements, elementsState⟩ := pair
        simp only [accepted, bind, Except.bind] at success
        exact generated accepted (Except.ok.inj success).symm

end Solcore.SourceSemantics.SourceInferenceSoundness
