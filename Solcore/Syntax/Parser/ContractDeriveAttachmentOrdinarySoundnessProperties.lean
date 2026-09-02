import Solcore.Syntax.DeclarativeContractDeriveAttachmentGrammar
import Solcore.Syntax.Parser.Contract
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Exact executable reflection for contract-member derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every successful derive attachment performs the exact pure AST
transformation and leaves the declarative parser remainder unchanged. -/
theorem attachContractDerive_success_ordinaryOutcome_sound
    {derive : DeriveAttribute} {member attached : ContractMember}
    {input output : State}
    (result : attachContractDerive derive member input = .ok attached output) :
    DeclarativeGrammar.ContractDeriveAttaches derive member attached ∧
      output.declarativeRemainder = input.declarativeRemainder := by
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue with
  | field declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.field, rfl⟩
  | function declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.function, rfl⟩
  | constructor declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.constructor, rfl⟩
  | fallback declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.fallback, rfl⟩
  | typeAlias declaration =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.typeAlias, rfl⟩
  | enum declaration =>
      simp only [attachContractDerive, pure] at result
      cases result
      exact ⟨.enum, rfl⟩
  | error =>
      simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
        at result
      cases result
      exact ⟨.error, rfl⟩

/-- Derive attachment is an unconditional ordinary success for every member
variant and parser state. -/
theorem attachContractDerive_total_success
    (derive : DeriveAttribute) (member : ContractMember) (input : State) :
    ∃ attached output,
      attachContractDerive derive member input = .ok attached output := by
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue <;>
    simp [attachContractDerive, emitDiagnostic, modifyState, bind, pure]

end Solcore.Syntax.Parser.ContractInternals
