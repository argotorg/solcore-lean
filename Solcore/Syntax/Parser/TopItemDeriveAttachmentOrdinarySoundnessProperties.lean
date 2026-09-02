import Solcore.Syntax.DeclarativeTopItemDeriveAttachmentProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.File

/-! Exact executable reflection for top-item derive attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every successful derive attachment performs the exact pure AST
transformation and leaves the declarative parser remainder unchanged. -/
theorem attachDeriveAttribute_success_ordinaryOutcome_sound
    {derive : DeriveAttribute} {item attached : TopItem}
    {input output : State}
    (result : attachDeriveAttribute derive item input = .ok attached output) :
    DeclarativeGrammar.TopItemDeriveAttaches derive item attached ∧
      output.declarativeRemainder = input.declarativeRemainder := by
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue with
  | importDecl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.importDecl, rfl⟩
  | exportDecl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.exportDecl, rfl⟩
  | pragmaDecl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.pragmaDecl, rfl⟩
  | typeAlias declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.typeAlias, rfl⟩
  | enum declaration =>
      simp only [attachDeriveAttribute, pure] at result
      cases result
      exact ⟨.enum, rfl⟩
  | trait declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.trait, rfl⟩
  | impl declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.impl, rfl⟩
  | contract declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.contract, rfl⟩
  | function declaration =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.function, rfl⟩
  | error =>
      simp only [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
        modifyState, bind, pure] at result
      cases result
      exact ⟨.error, rfl⟩

/-- Top-item derive attachment is an unconditional ordinary success for every
item variant and parser state. -/
theorem attachDeriveAttribute_total_success
    (derive : DeriveAttribute) (item : TopItem) (input : State) :
    ∃ attached output,
      attachDeriveAttribute derive item input = .ok attached output := by
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue <;>
    simp [attachDeriveAttribute, extendTopItemStart, emitDiagnostic,
      modifyState, bind, pure]

end Solcore.Syntax.Parser.FileInternals
