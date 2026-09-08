import Solcore.Frontend.LocalReference

/-! An additive canonical adapter for identifiers, grouping, conditionals, and
the Boolean operators `!`, `&&`, and `||`, and Word complement `~`. Its explicit
name table supplies all identities, including any bindings for `true` or `false`.
Literal interpretation, other operators, source bindings, and global resolution remain
outside this fragment. Unsupported syntax is not a source-language rejection. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Resolve every child of a supported expression, preserving conditional shape.
Grouping and source ranges are ignored. No lexical or span validity is assumed;
resolution itself assigns no types or truthiness conversions. -/
def resolveLocalExpression? (table : LocalNameTable) (source : Syntax.Expr) :
    Option Resolved.Expr :=
  match source with
  | ⟨_, .identifier name⟩ => (table.lookup? name.value).map Resolved.Expr.var
  | ⟨_, .group inner⟩ => resolveLocalExpression? table inner
  | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ =>
      (resolveLocalExpression? table operand).map (Resolved.Expr.unary .boolNot)
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      (resolveLocalExpression? table operand).map (Resolved.Expr.unary .wordNot)
  | ⟨_, .binary left ⟨_, .logicalAnd⟩ right⟩ => do
      return .ifE (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right) (.bool false)
  | ⟨_, .binary left ⟨_, .logicalOr⟩ right⟩ => do
      return .ifE (← resolveLocalExpression? table left) (.bool true)
        (← resolveLocalExpression? table right)
  | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ => do
      return .ifE (← resolveLocalExpression? table condition)
        (← resolveLocalExpression? table thenBranch) (← resolveLocalExpression? table elseBranch)
  | _ => none
termination_by sizeOf source

/-- Independent structural resolution requires every written child, including
both short-circuit operands. Inserted Boolean values are not source-name lookups. -/
inductive ResolvesLocalExpression (table : LocalNameTable) :
    Syntax.Expr → Resolved.Expr → Prop where
  | identifier {span : Syntax.SourceSpan} {name : Syntax.Identifier} {id : Resolved.LocalId}
      (found : LocalNameTable.Lookup table name.value id) :
      ResolvesLocalExpression table { span, value := .identifier name } (.var id)
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {resolved : Resolved.Expr}
      (child : ResolvesLocalExpression table inner resolved) :
      ResolvesLocalExpression table { span, value := .group inner } resolved
  | logicalNot {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {resolvedOperand : Resolved.Expr}
      (operandChild : ResolvesLocalExpression table operand resolvedOperand) :
      ResolvesLocalExpression table
        { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand }
        (.unary .boolNot resolvedOperand)
  | bitNot {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {resolvedOperand : Resolved.Expr}
      (operandChild : ResolvesLocalExpression table operand resolvedOperand) :
      ResolvesLocalExpression table
        { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand }
        (.unary .wordNot resolvedOperand)
  | logicalAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right }
        (.ifE resolvedLeft resolvedRight (.bool false))
  | logicalOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right }
        (.ifE resolvedLeft (.bool true) resolvedRight)
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr}
      {resolvedCondition resolvedThen resolvedElse : Resolved.Expr}
      (conditionChild : ResolvesLocalExpression table condition resolvedCondition)
      (thenChild : ResolvesLocalExpression table thenBranch resolvedThen)
      (elseChild : ResolvesLocalExpression table elseBranch resolvedElse) :
      ResolvesLocalExpression table
        { span, value := .conditional condition question thenBranch colon elseBranch }
        (.ifE resolvedCondition resolvedThen resolvedElse)

end Solcore.Frontend
