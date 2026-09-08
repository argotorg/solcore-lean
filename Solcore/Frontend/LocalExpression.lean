import Solcore.Frontend.LocalReference
import Solcore.Frontend.WordLiteral

/-! An additive canonical adapter for identifiers, strict Word literals, grouping,
conditionals, Boolean operators, Word arithmetic/bitwise operators, unsigned
Word comparisons and equality/inequality. Its explicit name table
supplies identities, including any bindings for `true` or `false`; literals do
not consult that table. This fixed literal interpretation is local to the adapter,
not a general source conversion or overload policy. Other expression forms,
source bindings, and global resolution remain outside this fragment. Unsupported syntax
is not a source-language rejection. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Resolve every child of a supported expression, preserving conditional shape.
Grouping and source ranges are ignored. No lexical or span validity is assumed;
literal conversion is strict Word-only and no truthiness conversion is performed. -/
def resolveLocalExpression? (table : LocalNameTable) (source : Syntax.Expr) :
    Option Resolved.Expr :=
  match source with
  | ⟨_, .identifier name⟩ => (table.lookup? name.value).map Resolved.Expr.var
  | ⟨_, .literal literal⟩ => (interpretWordLiteral? literal).map Resolved.Expr.word
  | ⟨_, .group inner⟩ => resolveLocalExpression? table inner
  | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ =>
      (resolveLocalExpression? table operand).map (Resolved.Expr.unary .boolNot)
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      (resolveLocalExpression? table operand).map (Resolved.Expr.unary .wordNot)
  | ⟨_, .binary left ⟨_, .add⟩ right⟩ => do
      return .binary .wordAdd (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ => do
      return .binary .wordSub (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .multiply⟩ right⟩ => do
      return .binary .wordMul (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .divide⟩ right⟩ => do
      return .binary .wordDiv (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .modulo⟩ right⟩ => do
      return .binary .wordMod (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .greater⟩ right⟩ => do
      return .binary .wordGt (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .equal⟩ right⟩ => do
      return .binary .wordEq (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .notEqual⟩ right⟩ => do
      return .unary .boolNot (.binary .wordEq (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right))
  | ⟨_, .binary left ⟨_, .lessEqual⟩ right⟩ => do
      return .unary .boolNot (.binary .wordGt (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right))
  | ⟨_, .binary left ⟨_, .less⟩ right⟩ => do
      return .wordLt (← resolveLocalExpression? table left) (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .greaterEqual⟩ right⟩ => do
      return .unary .boolNot (.wordLt (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right))
  | ⟨_, .binary left ⟨_, .bitAnd⟩ right⟩ => do
      return .binary .wordAnd (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .bitOr⟩ right⟩ => do
      return .binary .wordOr (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
  | ⟨_, .binary left ⟨_, .bitXor⟩ right⟩ => do
      return .binary .wordXor (← resolveLocalExpression? table left)
        (← resolveLocalExpression? table right)
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
  | wordLiteral {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteral} {word : Core.Word}
      (meaning : WordLiteralDenotes literal word) :
      ResolvesLocalExpression table { span, value := .literal literal } (.word word)
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
  | add {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .add⟩ right }
        (.binary .wordAdd resolvedLeft resolvedRight)
  | subtract {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .subtract⟩ right }
        (.binary .wordSub resolvedLeft resolvedRight)
  | multiply {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .multiply⟩ right }
        (.binary .wordMul resolvedLeft resolvedRight)
  | divide {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .divide⟩ right }
        (.binary .wordDiv resolvedLeft resolvedRight)
  | modulo {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .modulo⟩ right }
        (.binary .wordMod resolvedLeft resolvedRight)
  | greater {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
        (.binary .wordGt resolvedLeft resolvedRight)
  | equal {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
        (.binary .wordEq resolvedLeft resolvedRight)
  | notEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
        (.unary .boolNot (.binary .wordEq resolvedLeft resolvedRight))
  | lessEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right }
        (.unary .boolNot (.binary .wordGt resolvedLeft resolvedRight))
  | less {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .less⟩ right }
        (.wordLt resolvedLeft resolvedRight)
  | greaterEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right }
        (.unary .boolNot (.wordLt resolvedLeft resolvedRight))
  | bitAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right }
        (.binary .wordAnd resolvedLeft resolvedRight)
  | bitOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right }
        (.binary .wordOr resolvedLeft resolvedRight)
  | bitXor {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right }
        (.binary .wordXor resolvedLeft resolvedRight)
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
