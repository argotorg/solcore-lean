import Solcore.Syntax.DeclarativeContractDeriveAttachmentGrammar

/-! Functional and total laws for pure contract-member derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Attaching one derive attribute to one contract member has one exact AST
result. -/
theorem ContractDeriveAttaches.output_unique
    {derive : Syntax.DeriveAttribute} {member left right : Syntax.ContractMember}
    (leftAttached : ContractDeriveAttaches derive member left)
    (rightAttached : ContractDeriveAttaches derive member right) :
    left = right := by
  cases leftAttached <;> cases rightAttached <;> rfl

/-- Every contract-member variant has an exact derive-attachment result. -/
theorem ContractDeriveAttaches.exists
    (derive : Syntax.DeriveAttribute) (member : Syntax.ContractMember) :
    ∃ output, ContractDeriveAttaches derive member output := by
  rcases member with ⟨memberSpan, leadingComments, value⟩
  cases value with
  | field declaration =>
      exact ⟨_, .field⟩
  | function declaration =>
      exact ⟨_, .function⟩
  | constructor declaration =>
      exact ⟨_, .constructor⟩
  | fallback declaration =>
      exact ⟨_, .fallback⟩
  | typeAlias declaration =>
      exact ⟨_, .typeAlias⟩
  | enum declaration =>
      exact ⟨_, .enum⟩
  | error =>
      exact ⟨_, .error⟩

end Solcore.Syntax.DeclarativeGrammar
