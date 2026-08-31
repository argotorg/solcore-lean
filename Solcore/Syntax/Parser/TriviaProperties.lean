import Solcore.Syntax.Parser.Trivia
import Solcore.Syntax.FileValidity

/-! Source-validity preservation for canonical comment attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Selected leading comments inherit validity from the complete comment stream. -/
theorem commentsDirectlyBefore_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declarationStart : Nat) :
    ∀ comment ∈ commentsDirectlyBefore file.content comments
      declarationStart, comment.span.ValidFor file := by
  intro comment member
  exact commentsValid comment
    (commentsDirectlyBefore_mem file.content comments declarationStart member)

namespace TriviaInternals

/-- Attaching selected comments preserves a valid trait method. -/
theorem attachTraitMethodComments_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (method : TraitMethod) (methodValid : TraitMethod.ValidFor file method) :
    TraitMethod.ValidFor file
      (attachTraitMethodComments file comments method) := by
  rcases methodValid with
    ⟨spanValid, _oldCommentsValid, signatureValid, semicolonValid⟩
  refine ⟨spanValid, ?_, signatureValid, semicolonValid⟩
  exact commentsDirectlyBefore_validFor file comments commentsValid
    method.value.signature.span.startByte

/-- Mapping trait-method comments leaves every declaration range valid. -/
theorem attachTraitComments_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declaration : TraitDecl)
    (declarationValid : TraitDecl.ValidFor file declaration) :
    TraitDecl.ValidFor file
      (attachTraitComments file comments declaration) := by
  rcases declarationValid with
    ⟨spanValid, nameValid, parametersSpanValid, parametersValid,
      whereValid, bodyValid, methodsValid⟩
  refine ⟨spanValid, nameValid, parametersSpanValid, parametersValid,
    whereValid, bodyValid, ?_⟩
  intro attached attachedMember
  rcases List.mem_map.mp attachedMember with
    ⟨method, methodMember, rfl⟩
  exact attachTraitMethodComments_validFor file comments commentsValid method
    (methodsValid method methodMember)

/-- Attaching selected comments preserves a valid implementation method. -/
theorem attachImplMethodComments_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (method : ImplMethod)
    (methodValid : ImplMethod.ValidFor statementValid file method) :
    ImplMethod.ValidFor statementValid file
      (attachImplMethodComments file comments method) := by
  rcases methodValid with
    ⟨spanValid, _oldCommentsValid, declarationValid⟩
  refine ⟨spanValid, ?_, declarationValid⟩
  exact commentsDirectlyBefore_validFor file comments commentsValid
    method.span.startByte

/-- Mapping implementation-method comments preserves declaration validity. -/
theorem attachImplComments_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (declaration : ImplDecl)
    (declarationValid : ImplDecl.ValidFor statementValid file declaration) :
    ImplDecl.ValidFor statementValid file
      (attachImplComments file comments declaration) := by
  rcases declarationValid with
    ⟨spanValid, defaultValid, parameterSpanValid, parametersValid,
      traitNameValid, headSpanValid, headArgumentsValid, whereValid,
      bodyValid, methodsValid⟩
  refine ⟨spanValid, defaultValid, parameterSpanValid, parametersValid,
    traitNameValid, headSpanValid, headArgumentsValid, whereValid,
    bodyValid, ?_⟩
  intro attached attachedMember
  rcases List.mem_map.mp attachedMember with
    ⟨method, methodMember, rfl⟩
  exact attachImplMethodComments_validFor statementValid file comments
    commentsValid method (methodsValid method methodMember)

end TriviaInternals

/-- Public top-level attachment selects only source-valid leading comments. -/
theorem attachTopItemComments_leading_validFor (file : SourceFile)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (item : TopItem) :
    ∀ comment ∈ (attachTopItemComments file comments item).leadingComments,
      comment.span.ValidFor file := by
  exact commentsDirectlyBefore_validFor file comments commentsValid
    item.span.startByte

/-- The public top-level trait branch preserves its nested declaration contract. -/
theorem attachTopItemComments_trait_validFor (file : SourceFile)
    (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (span : SourceSpan) (leadingComments : List Comment)
    (spanValid : span.ValidFor file)
    (declaration : TraitDecl)
    (declarationValid : TraitDecl.ValidFor file declaration) :
    TopItem.ValidFor statementValid expressionValid file
      (attachTopItemComments file comments {
        span, leadingComments, value := .trait declaration
      }) := by
  apply TopItem.ValidFor.trait
  · exact spanValid
  · exact commentsDirectlyBefore_validFor file comments commentsValid
      span.startByte
  · exact TriviaInternals.attachTraitComments_validFor file comments
      commentsValid declaration declarationValid

/-- The public top-level impl branch preserves its nested declaration contract. -/
theorem attachTopItemComments_impl_validFor
    (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (comments : List Comment)
    (commentsValid : ∀ comment ∈ comments, comment.span.ValidFor file)
    (span : SourceSpan) (leadingComments : List Comment)
    (spanValid : span.ValidFor file)
    (declaration : ImplDecl)
    (declarationValid : ImplDecl.ValidFor statementValid file declaration) :
    TopItem.ValidFor statementValid expressionValid file
      (attachTopItemComments file comments {
        span, leadingComments, value := .impl declaration
      }) := by
  apply TopItem.ValidFor.impl
  · exact spanValid
  · exact commentsDirectlyBefore_validFor file comments commentsValid
      span.startByte
  · exact TriviaInternals.attachImplComments_validFor statementValid file
      comments commentsValid declaration declarationValid

end Solcore.Syntax.Parser
