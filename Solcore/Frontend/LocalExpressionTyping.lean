import Solcore.Frontend.LocalExpression
import Solcore.Resolved.Typing

/-! Independent typing for the supported canonical local-expression fragment.
Logical negation and short-circuit operators require Boolean operands;
Word complement, addition/subtraction/multiplication, and bitwise operations require Word operands.
Unsigned Word greater-than and Word equality/inequality require two Words and return Bool.
Conditionals require a Boolean condition and equally typed branches. Numeric literals use the explicit strict
Word projection only in this monomorphic adapter. Names and local identities
come from caller tables; no general literal conversion or coercion is introduced. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalExpressionHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | identifier {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {id : Resolved.LocalId} {type : Core.Ty}
      (named : LocalNameTable.Lookup table name.value id)
      (found : Resolved.LocalScope.Lookup context id type) :
      LocalExpressionHasType table context { span, value := .identifier name } type
  | wordLiteral {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteral} {word : Core.Word}
      (meaning : WordLiteralDenotes literal word) :
      LocalExpressionHasType table context { span, value := .literal literal } .word
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {type : Core.Ty}
      (typing : LocalExpressionHasType table context inner type) :
      LocalExpressionHasType table context { span, value := .group inner } type
  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (operandTyped : LocalExpressionHasType table context operand .bool) :
      LocalExpressionHasType table context
        { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand } .bool
  | bitNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (operandTyped : LocalExpressionHasType table context operand .word) :
      LocalExpressionHasType table context
        { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand } .word
  | add {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .add⟩ right } .word
  | subtract {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .subtract⟩ right } .word
  | multiply {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .multiply⟩ right } .word
  | greater {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .greater⟩ right } .bool
  | equal {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .equal⟩ right } .bool
  | notEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right } .bool
  | bitAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right } .word
  | bitOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right } .word
  | bitXor {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right } .word
  | logicalAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .bool)
      (rightTyped : LocalExpressionHasType table context right .bool) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right } .bool
  | logicalOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .bool)
      (rightTyped : LocalExpressionHasType table context right .bool) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right } .bool
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr} {type : Core.Ty}
      (conditionTyped : LocalExpressionHasType table context condition .bool)
      (thenTyped : LocalExpressionHasType table context thenBranch type)
      (elseTyped : LocalExpressionHasType table context elseBranch type) :
      LocalExpressionHasType table context
        { span, value := .conditional condition question thenBranch colon elseBranch } type

/-- Resolve supported syntax, lower all references, and check the resulting
Core expression. Failure is adapter failure, not whole-language rejection. -/
def elaborateLocalExpression? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) := do
  let resolved ← resolveLocalExpression? table source
  let core ← resolved.lower? (Resolved.LocalScope.ids context)
  let type ← Core.infer? (Resolved.LocalScope.values context) core
  return (core, type)

end Solcore.Frontend
