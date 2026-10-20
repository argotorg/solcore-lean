import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! Ordered argument provenance records the actual expression calls and their
threaded states. It also represents a synthetic singleton list around a real
unary operand, without asserting that the list itself occurred in the run. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution

inductive OrderedExpressionCalls (provenance : CallIndex → Prop)
    (context : SourceInference.Context) :
    Nat → List Syntax.Expr → State → List InferredExpression → State → Prop where
  | nil {fuel : Nat} {state : State} :
      OrderedExpressionCalls provenance context (fuel + 1) [] state [] state
  | cons {fuel : Nat} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : inferExprFuel fuel context source none initial = .ok (value, middle))
      (here : provenance (.expression fuel context source none initial value middle))
      (tail : OrderedExpressionCalls provenance context fuel sources middle values final) :
      OrderedExpressionCalls provenance context (fuel + 1) (source :: sources)
        initial (value :: values) final

namespace OrderedExpressionCalls
variable {provenance : CallIndex → Prop} {context : SourceInference.Context}
    {fuel : Nat} {sources : List Syntax.Expr} {initial final : State}
    {values : List InferredExpression}

theorem accepted (calls : OrderedExpressionCalls provenance context fuel sources initial values final) :
    inferExprsFuel fuel context sources initial = .ok (values, final) := by
  induction calls with
  | nil => simp only [inferExprsFuel]
  | cons accepted _ _ induction =>
      simp only [inferExprsFuel, accepted, bind, Except.bind, induction, pure, Pure.pure, Except.pure]

/-- Exact successful head and tail results recover their recorded provenance. -/
theorem split {source : Syntax.Expr} {middle : State} {value : InferredExpression}
    (calls : OrderedExpressionCalls provenance context (fuel + 1) (source :: sources)
      initial (value :: values) final)
    (headAccepted : inferExprFuel fuel context source none initial = .ok (value, middle)) :
    provenance (.expression fuel context source none initial value middle) ∧
      OrderedExpressionCalls provenance context fuel sources middle values final := by
  cases calls with
  | cons actual here tail =>
      have same := Except.ok.inj (actual.symm.trans headAccepted)
      cases Prod.mk.inj same with
      | intro sameValue sameState =>
          cases sameValue
          cases sameState
          exact ⟨here, tail⟩

theorem of_call (descend : ChildClosed provenance) :
    ∀ {fuel : Nat} {sources : List Syntax.Expr} {initial final : State}
      {values : List InferredExpression},
    provenance (.expressions fuel context sources initial values final) →
    inferExprsFuel fuel context sources initial = .ok (values, final) →
    OrderedExpressionCalls provenance context fuel sources initial values final := by
  intro fuel
  induction fuel with
  | zero =>
      intro sources initial final values _ accepted
      simp only [inferExprsFuel] at accepted
      cases accepted
  | succ fuel induction =>
      intro sources initial final values here accepted
      cases sources with
      | nil =>
          simp only [inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          exact .nil
      | cons source sources =>
          have parentAccepted := accepted
          unfold inferExprsFuel at accepted
          cases headAccepted : inferExprFuel fuel context source none initial with
          | error error => simp [headAccepted, bind, Except.bind] at accepted
          | ok pair =>
              rcases pair with ⟨head, middle⟩
              simp only [headAccepted, bind, Except.bind] at accepted
              cases tailAccepted : inferExprsFuel fuel context sources middle with
              | error error => simp [tailAccepted] at accepted
              | ok pair =>
                  rcases pair with ⟨tail, tailFinal⟩
                  simp only [tailAccepted, pure, Pure.pure, Except.pure, Except.ok.injEq,
                    Prod.mk.injEq] at accepted
                  rcases accepted with ⟨rfl, rfl⟩
                  exact .cons headAccepted
                    (descend here (.expressions_head parentAccepted headAccepted))
                    (induction (descend here (.expressions_tail parentAccepted headAccepted tailAccepted))
                      tailAccepted)

theorem of_accepted
    (accepted : inferExprsFuel fuel context sources initial = .ok (values, final)) :
    OrderedExpressionCalls (fun _ => True) context fuel sources initial values final :=
  of_call true_childClosed trivial accepted

/-- A real operand call can be used as a singleton argument sequence. -/
theorem singleton {source : Syntax.Expr} {value : InferredExpression}
    (accepted : inferExprFuel fuel context source none initial = .ok (value, final))
    (here : provenance (.expression fuel context source none initial value final)) :
    OrderedExpressionCalls provenance context (fuel + 1) [source] initial [value] final := by
  cases fuel with
  | zero =>
      simp only [inferExprFuel] at accepted
      cases accepted
  | succ fuel => exact .cons accepted here .nil

end OrderedExpressionCalls
end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
