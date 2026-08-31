import Solcore.Syntax.SignatureValidity

/-! External consumers for canonical signature source validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Predicate.ValidFor
example := @WhereClause.ValidFor
example := @FunctionModifiers.ValidFor
example := @ReturnClause.ValidFor
example := @FunctionSignature.ValidFor

example (file : SourceFile) (signature : FunctionSignature)
    (valid : FunctionSignature.ValidFor file signature) :
    signature.span.ValidFor file ∧
      signature.name.span.ValidFor file ∧
      signature.parameters.span.ValidFor file :=
  ⟨valid.1, valid.2.1, valid.2.2.2.2.1⟩

example (file : SourceFile) (clause : ReturnClause)
    (valid : ReturnClause.ValidFor file clause)
    (type : TypeExpr) (member : type ∈ clause.types.elements) :
    clause.span.ValidFor file ∧ TypeExpr.ValidFor file type :=
  ⟨valid.1, valid.2.2 type member⟩

end Tests
