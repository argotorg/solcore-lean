import Solcore.Syntax.Term

/-! A spelling-avoidance condition only for the supported local-expression
fragment. This is not a free-name analysis for other canonical syntax forms. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- No identifier in this identifier/group/logical-negation/conditional expression has the
specified spelling. All conditional children are checked, not just a branch
that a particular runtime environment might select. -/
inductive AvoidsLocalName (name : String) : Syntax.Expr → Prop where
  | identifier {span : Syntax.SourceSpan} {identifier : Syntax.Identifier}
      (different : name ≠ identifier.value) :
      AvoidsLocalName name { span, value := .identifier identifier }
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      (child : AvoidsLocalName name inner) :
      AvoidsLocalName name { span, value := .group inner }
  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : AvoidsLocalName name operand) :
      AvoidsLocalName name { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand }
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr}
      (conditionAvoids : AvoidsLocalName name condition)
      (thenAvoids : AvoidsLocalName name thenBranch)
      (elseAvoids : AvoidsLocalName name elseBranch) :
      AvoidsLocalName name
        { span, value := .conditional condition question thenBranch colon elseBranch }

end Solcore.Frontend
