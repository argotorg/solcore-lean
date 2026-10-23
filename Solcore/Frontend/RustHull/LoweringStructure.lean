import Solcore.Frontend.RustHull.LoweringSafety

/-! Decomposition of successful calls to the actual Hull compiler. Semantic
proofs use these results to recover the generated terms and the compiler's
annotation checks, rather than assuming a second translation agrees with it. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull

theorem lowerExpression_pair_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type : Ty} {span : Option Span} {left right : Expr} {lowered : Lowered}
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, .pair left right, span⟩ = .ok lowered) :
    ∃ leftCode rightCode,
      lowerExpression fuel signatures scope left = .ok leftCode ∧
      lowerExpression fuel signatures scope right = .ok rightCode ∧
      lowered = ⟨.product leftCode.type rightCode.type,
        Core.LocalSequence.pair leftCode.type rightCode.type
          leftCode.expression rightCode.expression⟩ := by
  simp only [lowerExpression] at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨leftCode, leftAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨rightCode, rightAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
  cases checked
  cases returned
  exact ⟨leftCode, rightCode, leftAccepted, rightAccepted, rfl⟩

end Solcore.Frontend.RustHull
