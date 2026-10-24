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

theorem lowerExpression_projection_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type : Ty} {span : Option Span} {operand : Expr} {lowered : Lowered}
    (right : Bool)
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, if right then .snd operand else .fst operand, span⟩ = .ok lowered) :
    ∃ value leftType rightType,
      lowerExpression fuel signatures scope operand = .ok value ∧
      value.type = .product leftType rightType ∧
      lowered = ⟨if right then rightType else leftType,
        Core.LanguageResult.bind (if right then rightType else leftType) value.expression
          (Core.LanguageResult.success
            (if right then .second (.var 0) else .first (.var 0)))⟩ := by
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, lowerExpression] at accepted
  all_goals
    obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨value, valueAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
    cases shape : value.type <;> simp only [shape] at accepted
    all_goals try { simp [fail, lower_bind_eq_ok] at accepted }
    dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
    obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
    cases checked
    cases returned
    exact ⟨value, _, _, valueAccepted, shape, rfl⟩

theorem lowerExpression_injection_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type target : Ty} {span : Option Span} {operand : Expr} {lowered : Lowered}
    (right : Bool)
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ = .ok lowered) :
    ∃ value leftType rightType,
      lowerType fuel target = .ok (.sum leftType rightType) ∧
      lowerExpression fuel signatures scope operand = .ok value ∧
      value.type = (if right then rightType else leftType) ∧
      lowered = ⟨.sum leftType rightType,
        Core.LanguageResult.bind (.sum leftType rightType) value.expression
          (Core.LanguageResult.success
            (if right then .inRight leftType (.var 0) else .inLeft rightType (.var 0)))⟩ := by
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte, lowerExpression] at accepted
  all_goals
    obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨targetType, targetAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨value, valueAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
    cases shape : targetType <;> simp only [shape] at accepted
    all_goals try { simp [fail, lower_bind_eq_ok] at accepted }
    dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
    obtain ⟨checked, matched, accepted⟩ := lower_bind_eq_ok.mp accepted
    cases checked
    have payload := expectType_eq_of_ok matched
    dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
    obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
    cases checked
    cases returned
    exact ⟨value, _, _, shape ▸ targetAccepted, valueAccepted, payload.symm, rfl⟩

theorem lowerExpression_conditional_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type target : Ty} {span : Option Span} {conditionExpr yes no : Expr} {lowered : Lowered}
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, .ifThen target conditionExpr yes no, span⟩ = .ok lowered) :
    ∃ conditionCode test yesCode noCode,
      lowerExpression fuel signatures scope conditionExpr = .ok conditionCode ∧
      condition conditionCode = .ok test ∧
      lowerExpression fuel signatures scope yes = .ok yesCode ∧
      lowerExpression fuel signatures scope no = .ok noCode ∧
      yesCode.type = lowered.type ∧ noCode.type = lowered.type ∧
      lowered.expression = Core.LocalControl.choose lowered.type test yesCode.expression noCode.expression := by
  simp only [lowerExpression] at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨targetType, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨conditionCode, conditionAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨test, testAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨yesCode, yesAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨noCode, noAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨yesCheck, yesMatched, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases yesCheck
  obtain ⟨noCheck, noMatched, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases noCheck
  dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
  cases checked
  cases returned
  exact ⟨conditionCode, test, yesCode, noCode, conditionAccepted, testAccepted, yesAccepted,
    noAccepted, (expectType_eq_of_ok yesMatched).symm, (expectType_eq_of_ok noMatched).symm, rfl⟩

theorem lowerExpression_indexedInjection_components {fuel : Nat} {signatures : List Signature}
    {scope : Scope} {type target : Ty} {span : Option Span} {operand : Expr} {index : Nat}
    {lowered : Lowered}
    (accepted : lowerExpression (fuel + 1) signatures scope
      ⟨type, .inK index target operand, span⟩ = .ok lowered) :
    ∃ value targetType injected,
      lowerType fuel target = .ok targetType ∧
      lowerExpression fuel signatures scope operand = .ok value ∧
      inject index targetType value.type (.var 0) = .ok injected ∧
      lowered = ⟨targetType, Core.LanguageResult.bind targetType value.expression
        (Core.LanguageResult.success injected)⟩ := by
  simp only [lowerExpression] at accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨targetType, targetAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨value, valueAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨injected, injectionAccepted, accepted⟩ := lower_bind_eq_ok.mp accepted
  dsimp only [Bind.bind, Except.bind, Pure.pure] at accepted
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
  cases checked
  cases returned
  exact ⟨value, targetType, injected, targetAccepted, valueAccepted, injectionAccepted, rfl⟩

end Solcore.Frontend.RustHull
