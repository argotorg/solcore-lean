import Solcore.Frontend.LocalReference

/-! An additive canonical identifier/group/logical-negation/conditional adapter. Its explicit
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
  | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ => do
      return .ifE (← resolveLocalExpression? table condition)
        (← resolveLocalExpression? table thenBranch) (← resolveLocalExpression? table elseBranch)
  | _ => none
termination_by sizeOf source

/-- Independent structural resolution: all three conditional children must
resolve, even though subsequent evaluation can select just one branch. -/
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
