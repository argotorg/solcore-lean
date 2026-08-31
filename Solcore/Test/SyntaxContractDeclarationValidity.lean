import Solcore.Syntax.ContractDeclarationValidity

/-! External consumers for canonical contract declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @ContractField.ValidFor
example := @ConstructorDecl.ValidFor
example := @FallbackDecl.ValidFor
example := @ContractMember.ValidFor
example := @ContractDecl.ValidFor

example (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (declaration : ContractDecl)
    (valid : ContractDecl.ValidFor statementValid expressionValid
      file declaration)
    (member : ContractMember)
    (retained : member ∈ declaration.value.members) :
    declaration.value.bodySpan.ValidFor file ∧
      ContractMember.ValidFor statementValid expressionValid file member :=
  ⟨valid.2.2.2.2.1, valid.2.2.2.2.2 member retained⟩

end Tests
