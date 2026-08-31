import Solcore.Syntax.CallableDeclarationValidity
import Solcore.Syntax.TypeDeclarationValidity

/-! Source-validity contracts for canonical contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace ContractField

/-- A contract field retains valid name, type, and initializer ranges. -/
def ValidFor (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (field : ContractField) : Prop :=
  field.span.ValidFor file ∧
    field.value.name.span.ValidFor file ∧
    TypeExpr.ValidFor file field.value.type ∧
    ∀ initializer ∈ field.value.initializer,
      expressionValid file initializer

end ContractField

namespace ConstructorDecl

/-- Every parameter, modifier, and body range in a constructor is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : ConstructorDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.parameters.span.ValidFor file ∧
    (∀ parameter ∈ declaration.value.parameters.elements,
      FunctionParameter.ValidFor file parameter) ∧
    (∀ marker ∈ declaration.value.payableMarker, marker.ValidFor file) ∧
    declaration.value.body.span.ValidFor file ∧
    ∀ statement ∈ declaration.value.body.value,
      statementValid file statement

end ConstructorDecl

namespace FallbackDecl

/-- Every parameter, modifier, and body range in a fallback is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : FallbackDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.parameters.span.ValidFor file ∧
    (∀ parameter ∈ declaration.value.parameters.elements,
      FunctionParameter.ValidFor file parameter) ∧
    (∀ marker ∈ declaration.value.payableMarker, marker.ValidFor file) ∧
    declaration.value.body.span.ValidFor file ∧
    ∀ statement ∈ declaration.value.body.value,
      statementValid file statement

end FallbackDecl

namespace ContractMember

/-- Every range retained by one contract member belongs to one source. -/
inductive ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : ContractMember → Prop where
  | field {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ContractField}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ContractField.ValidFor expressionValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .field declaration
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
  | constructor {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ConstructorDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ConstructorDecl.ValidFor statementValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .constructor declaration
      }
  | fallback {span : SourceSpan} {leadingComments : List Comment}
      {declaration : FallbackDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : FallbackDecl.ValidFor statementValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .fallback declaration
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
  | error {span : SourceSpan} {leadingComments : List Comment}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .error
      }

end ContractMember

namespace ContractDecl

/-- Every range retained by a complete contract declaration is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (declaration : ContractDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      ∀ parameter ∈ parameters.elements.toList,
        parameter.span.ValidFor file) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ member ∈ declaration.value.members,
      ContractMember.ValidFor statementValid expressionValid file member

end ContractDecl

end Solcore.Syntax
