import Solcore.Syntax.Term

/-! A spelling-avoidance condition for the local-expression shapes. Every literal
payload avoids all names, even if malformed, overflowing, or a string. This is
not a free-name analysis for other canonical syntax forms. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- No identifier in this expression has the specified spelling. Literal validity
is not required, since literal payloads do not perform name lookup.
All conditional children and both operands of each binary form are checked, including
children that a particular runtime environment might skip. -/
inductive AvoidsLocalName (name : String) : Syntax.Expr → Prop where
  | identifier {span : Syntax.SourceSpan} {identifier : Syntax.Identifier}
      (different : name ≠ identifier.value) :
      AvoidsLocalName name { span, value := .identifier identifier }
  | literal {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteral} :
      AvoidsLocalName name { span, value := .literal literal }
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      (child : AvoidsLocalName name inner) :
      AvoidsLocalName name { span, value := .group inner }
  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : AvoidsLocalName name operand) :
      AvoidsLocalName name { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand }
  | bitNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : AvoidsLocalName name operand) :
      AvoidsLocalName name { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand }
  | add {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .add⟩ right }
  | subtract {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .subtract⟩ right }
  | multiply {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .multiply⟩ right }
  | greater {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
  | equal {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
  | notEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
  | bitAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right }
  | bitOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right }
  | bitXor {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right }
  | logicalAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right }
  | logicalOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right }
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr}
      (conditionAvoids : AvoidsLocalName name condition)
      (thenAvoids : AvoidsLocalName name thenBranch)
      (elseAvoids : AvoidsLocalName name elseBranch) :
      AvoidsLocalName name
        { span, value := .conditional condition question thenBranch colon elseBranch }

end Solcore.Frontend
