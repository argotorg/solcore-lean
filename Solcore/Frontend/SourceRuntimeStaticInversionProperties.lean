import Solcore.Frontend.SourceRuntime

/-! Inversion lemmas for the finite graph's executable static checker. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- A checked pair exposes both checked children and the product result. -/
theorem Expr.InfersType.pair_components
    {program : Program} {context : StaticContext}
    {left right : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.pair left right) expected) :
    ∃ leftType rightType,
      Expr.InfersType program context left leftType ∧
      Expr.InfersType program context right rightType ∧
      expected = .product leftType rightType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases leftResult : infer program context left with
  | error error =>
      simp [leftResult, bind, Except.bind] at inferredAt
  | ok leftStatic =>
      cases rightResult : infer program context right with
      | error error =>
          simp [leftResult, rightResult, bind, Except.bind] at inferredAt
      | ok rightStatic =>
          simp [leftResult, rightResult, bind, Except.bind] at inferredAt
          cases inferredAt
          exact ⟨leftStatic.erase, rightStatic.erase,
            ⟨leftStatic, leftResult, rfl⟩,
            ⟨rightStatic, rightResult, rfl⟩,
            by simpa [StaticType.erase] using erased.symm⟩

/-- A successful nonempty argument inference consists of a successful head
inference followed by successful inference of the tail, with no omitted or
reordered result types. -/
theorem inferList_cons_ok
    (program : Program) (context : StaticContext)
    (expression : Expr) (expressions : List Expr)
    (types : List StaticType)
    (success : inferList program context (expression :: expressions) =
      .ok types) :
    ∃ head tail,
      infer program context expression = .ok head ∧
      inferList program context expressions = .ok tail ∧
      types = head :: tail := by
  unfold inferList at success
  cases headResult : infer program context expression with
  | error error =>
      simp [headResult, bind, Except.bind] at success
  | ok head =>
      cases tailResult : inferList program context expressions with
      | error error =>
          simp [headResult, tailResult, bind, Except.bind] at success
      | ok tail =>
          simp [headResult, tailResult, bind, Except.bind] at success
          simp only [pure, Pure.pure, Except.pure] at success
          exact ⟨head, tail, rfl, rfl, (Except.ok.inj success).symm⟩

/-- Successful inference preserves argument-list length. -/
theorem inferList_ok_length
    (program : Program) (context : StaticContext) :
    ∀ (expressions : List Expr) (types : List StaticType),
      inferList program context expressions = .ok types →
      expressions.length = types.length := by
  intro expressions
  induction expressions with
  | nil =>
      intro types success
      simp [inferList] at success
      cases success
      rfl
  | cons expression expressions ih =>
      intro types success
      obtain ⟨head, tail, _, tailOk, typesEq⟩ :=
        inferList_cons_ok program context expression expressions types success
      subst types
      simp [ih tail tailOk]

end Solcore.Frontend.SourceRuntime
