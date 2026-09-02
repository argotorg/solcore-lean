import Solcore.Syntax.DeclarativeTopItemDeriveAttachmentGrammar

/-! Functional and total laws for pure top-item derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Attaching one derive attribute to one top-level item has one exact AST
result. -/
theorem TopItemDeriveAttaches.output_unique
    {derive : Syntax.DeriveAttribute} {item left right : Syntax.TopItem}
    (leftAttached : TopItemDeriveAttaches derive item left)
    (rightAttached : TopItemDeriveAttaches derive item right) :
    left = right := by
  cases leftAttached <;> cases rightAttached <;> rfl

/-- Every top-level item variant has an exact derive-attachment result. -/
theorem TopItemDeriveAttaches.exists
    (derive : Syntax.DeriveAttribute) (item : Syntax.TopItem) :
    ∃ output, TopItemDeriveAttaches derive item output := by
  rcases item with ⟨itemSpan, leadingComments, value⟩
  cases value with
  | importDecl declaration => exact ⟨_, .importDecl⟩
  | exportDecl declaration => exact ⟨_, .exportDecl⟩
  | pragmaDecl declaration => exact ⟨_, .pragmaDecl⟩
  | typeAlias declaration => exact ⟨_, .typeAlias⟩
  | enum declaration => exact ⟨_, .enum⟩
  | trait declaration => exact ⟨_, .trait⟩
  | impl declaration => exact ⟨_, .impl⟩
  | contract declaration => exact ⟨_, .contract⟩
  | function declaration => exact ⟨_, .function⟩
  | error => exact ⟨_, .error⟩

end Solcore.Syntax.DeclarativeGrammar
