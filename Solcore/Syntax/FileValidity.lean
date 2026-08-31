import Solcore.Syntax.ContractDeclarationValidity
import Solcore.Syntax.ModuleValidity

/-! Source-validity contracts for canonical top-level items and parsed files. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace TopItem

/-- Every range retained by one top-level item belongs to one source. -/
inductive ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : TopItem → Prop where
  | importDecl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ImportDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ImportDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .importDecl declaration
      }
  | exportDecl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ExportDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ExportDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .exportDecl declaration
      }
  | pragmaDecl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : PragmaDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : PragmaDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .pragmaDecl declaration
      }
  | typeAlias {span : SourceSpan} {leadingComments : List Comment}
      {declaration : TypeAliasDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : TypeAliasDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .typeAlias declaration
      }
  | enum {span : SourceSpan} {leadingComments : List Comment}
      {declaration : EnumDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : EnumDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .enum declaration
      }
  | trait {span : SourceSpan} {leadingComments : List Comment}
      {declaration : TraitDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : TraitDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .trait declaration
      }
  | impl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ImplDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ImplDecl.ValidFor statementValid file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .impl declaration
      }
  | contract {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ContractDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ContractDecl.ValidFor statementValid
        expressionValid file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .contract declaration
      }
  | function {span : SourceSpan} {leadingComments : List Comment}
      {declaration : FunctionDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : FunctionDecl.ValidFor statementValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .function declaration
      }
  | error {span : SourceSpan} {leadingComments : List Comment}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .error
      }

/-- A valid top-level item has a valid outer range. -/
theorem ValidFor.span_valid
    {statementValid : SourceFile → Statement → Prop}
    {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {item : TopItem}
    (valid : ValidFor statementValid expressionValid file item) :
    item.span.ValidFor file := by
  cases valid <;> assumption

/-- A valid top-level item retains only valid leading comments. -/
theorem ValidFor.comments_valid
    {statementValid : SourceFile → Statement → Prop}
    {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {item : TopItem}
    (valid : ValidFor statementValid expressionValid file item) :
    ∀ comment ∈ item.leadingComments, comment.span.ValidFor file := by
  cases valid <;> assumption

end TopItem

namespace ParsedFile

/-- A parsed file is owned by, and retains only ranges from, one source. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (parsed : ParsedFile) : Prop :=
  parsed.source = file.id ∧
    parsed.span.ValidFor file ∧
    (∀ item ∈ parsed.items,
      TopItem.ValidFor statementValid expressionValid file item) ∧
    ∀ comment ∈ parsed.comments, comment.span.ValidFor file

end ParsedFile

end Solcore.Syntax
