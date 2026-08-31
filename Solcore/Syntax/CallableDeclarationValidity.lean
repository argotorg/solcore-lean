import Solcore.Syntax.SignatureValidity

/-! Source-validity contracts for functions, traits, and implementations. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace FunctionDecl

/-- Every signature and body range retained by a function is source-valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : FunctionDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.signature.ValidFor file ∧
    declaration.value.body.span.ValidFor file ∧
    ∀ statement ∈ declaration.value.body.value,
      statementValid file statement

end FunctionDecl

namespace TraitMethod

/-- Every comment, signature, and terminator retained by a trait method is valid. -/
def ValidFor (file : SourceFile) (method : TraitMethod) : Prop :=
  method.span.ValidFor file ∧
    (∀ comment ∈ method.value.leadingComments,
      comment.span.ValidFor file) ∧
    method.value.signature.ValidFor file ∧
    method.value.semicolon.ValidFor file

end TraitMethod

namespace TraitDecl

/-- Every range retained by a complete trait declaration is source-valid. -/
def ValidFor (file : SourceFile) (declaration : TraitDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    declaration.value.genericParameters.span.ValidFor file ∧
    (∀ parameter ∈ declaration.value.genericParameters.elements.toList,
      parameter.span.ValidFor file) ∧
    (∀ clause ∈ declaration.value.whereClause,
      WhereClause.ValidFor file clause) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ method ∈ declaration.value.methods,
      TraitMethod.ValidFor file method

end TraitDecl

namespace ImplMethod

/-- An implementation method retains valid comments and a valid function. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (method : ImplMethod) : Prop :=
  method.span.ValidFor file ∧
    (∀ comment ∈ method.value.leadingComments,
      comment.span.ValidFor file) ∧
    FunctionDecl.ValidFor statementValid file method.value.declaration

end ImplMethod

namespace ImplDecl

/-- Every range retained by a complete implementation declaration is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : ImplDecl) : Prop :=
  declaration.span.ValidFor file ∧
    (∀ marker ∈ declaration.value.defaultMarker, marker.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      ∀ parameter ∈ parameters.elements.toList,
        parameter.span.ValidFor file) ∧
    declaration.value.traitName.span.ValidFor file ∧
    declaration.value.headArguments.span.ValidFor file ∧
    (∀ argument ∈ declaration.value.headArguments.elements.toList,
      TypeExpr.ValidFor file argument) ∧
    (∀ clause ∈ declaration.value.whereClause,
      WhereClause.ValidFor file clause) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ method ∈ declaration.value.methods,
      ImplMethod.ValidFor statementValid file method

end ImplDecl

end Solcore.Syntax
