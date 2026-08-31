import Solcore.Syntax.DeriveValidity
import Solcore.Syntax.TypeValidity

/-! Source-validity contracts for canonical type and enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace TypeAliasDecl

/-- Every range retained by a type alias belongs to one source. -/
def ValidFor (file : SourceFile) (declaration : TypeAliasDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    (∀ parameters ∈ declaration.value.parameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.parameters,
      ∀ parameter ∈ parameters.elements,
        parameter.span.ValidFor file) ∧
    TypeExpr.ValidFor file declaration.value.value

end TypeAliasDecl

namespace EnumConstructor

/-- Every comment, name, and field range retained by an enum case is valid. -/
def ValidFor (file : SourceFile) (constructor : EnumConstructor) : Prop :=
  constructor.span.ValidFor file ∧
    (∀ comment ∈ constructor.value.leadingComments,
      comment.span.ValidFor file) ∧
    constructor.value.name.span.ValidFor file ∧
    (∀ fields ∈ constructor.value.fields, fields.span.ValidFor file) ∧
    ∀ fields ∈ constructor.value.fields,
      ∀ field ∈ fields.elements, TypeExpr.ValidFor file field

end EnumConstructor

namespace EnumDecl

/-- Every range retained by a complete enum declaration is source-valid. -/
def ValidFor (file : SourceFile) (declaration : EnumDecl) : Prop :=
  declaration.span.ValidFor file ∧
    (∀ retained ∈ declaration.value.deriveAttribute,
      DeriveAttribute.ValidFor file retained) ∧
    declaration.value.name.span.ValidFor file ∧
    (∀ parameters ∈ declaration.value.parameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.parameters,
      ∀ parameter ∈ parameters.elements.toList,
        parameter.span.ValidFor file) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ constructor ∈ declaration.value.constructors,
      EnumConstructor.ValidFor file constructor

end EnumDecl

end Solcore.Syntax
