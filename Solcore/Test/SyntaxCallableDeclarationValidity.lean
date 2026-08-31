import Solcore.Syntax.CallableDeclarationValidity

/-! External consumers for callable declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @FunctionDecl.ValidFor
example := @TraitMethod.ValidFor
example := @TraitDecl.ValidFor
example := @ImplMethod.ValidFor
example := @ImplDecl.ValidFor

example (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : FunctionDecl)
    (valid : FunctionDecl.ValidFor statementValid file declaration)
    (statement : Statement)
    (member : statement ∈ declaration.value.body.value) :
    declaration.value.signature.ValidFor file ∧
      statementValid file statement :=
  ⟨valid.2.1, valid.2.2.2 statement member⟩

example (file : SourceFile) (declaration : TraitDecl)
    (valid : TraitDecl.ValidFor file declaration)
    (method : TraitMethod) (member : method ∈ declaration.value.methods) :
    declaration.value.bodySpan.ValidFor file ∧
      TraitMethod.ValidFor file method :=
  ⟨valid.2.2.2.2.2.1, valid.2.2.2.2.2.2 method member⟩

end Tests
