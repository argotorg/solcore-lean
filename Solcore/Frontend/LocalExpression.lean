import Solcore.Frontend.LocalReference
import Solcore.Frontend.WordLiteral

/-! An additive canonical adapter for identifiers, strict Word literals, grouping,
conditionals, Boolean operators, Word arithmetic/bitwise operators, unsigned
Word comparisons, equality/inequality and empty/right-associated tuples. Its explicit name table
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
  | ⟨_, .tuple ⟨_, []⟩⟩ => some .unit
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ => do
      return .pair (← resolveLocalExpression? table left) (← resolveLocalExpression? table right)
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ => do
      return .pair (← resolveLocalExpression? table first)
        (← resolveLocalExpression? table ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩)
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
  | unit {span tupleSpan : Syntax.SourceSpan} :
      ResolvesLocalExpression table { span, value := .tuple ⟨tupleSpan, []⟩ } .unit
  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {resolvedLeft resolvedRight : Resolved.Expr}
      (leftChild : ResolvesLocalExpression table left resolvedLeft)
      (rightChild : ResolvesLocalExpression table right resolvedRight) :
      ResolvesLocalExpression table
        { span, value := .tuple ⟨tupleSpan, [left, right]⟩ } (.pair resolvedLeft resolvedRight)
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {resolvedHead resolvedTail : Resolved.Expr}
      (headChild : ResolvesLocalExpression table first resolvedHead)
      (tailChild : ResolvesLocalExpression table
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ resolvedTail) :
      ResolvesLocalExpression table
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ (.pair resolvedHead resolvedTail)
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

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionShapeProperties`
-/

/-! Source ranges, identifier spelling, and grouping laws for the canonical
local-expression adapter. These laws do not depend on resolution correctness. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Changing the outer source range does not change structural resolution. -/
theorem resolveLocalExpression?_span (table : LocalNameTable) (source : Syntax.Expr)
    (span : Syntax.SourceSpan) :
    resolveLocalExpression? table { source with span } = resolveLocalExpression? table source := by
  cases source with
  | mk sourceSpan payload =>
      cases payload <;> try simp only [resolveLocalExpression?]
      case tuple elements =>
        cases elements with
        | mk tupleSpan elements =>
            cases elements with
            | nil => simp only [resolveLocalExpression?]
            | cons first remaining =>
                cases remaining with
                | nil => simp only [resolveLocalExpression?]
                | cons second tail =>
                    cases tail with
                    | nil => simp only [resolveLocalExpression?]
                    | cons third rest =>
                        have tailSame := resolveLocalExpression?_span table
                          ⟨sourceSpan, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ span
                        change resolveLocalExpression? table
                            ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ =
                          resolveLocalExpression? table
                            ⟨sourceSpan, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ at tailSame
                        conv => lhs; rw [resolveLocalExpression?]
                        conv => rhs; rw [resolveLocalExpression?]
                        rw [tailSame]
      case unary operator operand =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> simp only [resolveLocalExpression?]
      case binary left operator right =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> simp only [resolveLocalExpression?]
termination_by sizeOf source

/-- Literal spelling is retained, while both literal and outer ranges are ignored. -/
theorem resolveLocalExpression?_literal_spans (table : LocalNameTable)
    (payload : Syntax.CoreLiteralValue)
    (span literalSpan otherSpan otherLiteralSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table ⟨span, .literal ⟨literalSpan, payload⟩⟩ =
      resolveLocalExpression? table ⟨otherSpan, .literal ⟨otherLiteralSpan, payload⟩⟩ := by
  simp only [resolveLocalExpression?, interpretWordLiteral?]

/-- Conditional punctuation and the outer range carry no resolution meaning. -/
theorem resolveLocalExpression?_conditional_spans (table : LocalNameTable)
    (condition thenBranch elseBranch : Syntax.Expr)
    (span question colon otherSpan otherQuestion otherColon : Syntax.SourceSpan) :
    resolveLocalExpression? table
        { span, value := .conditional condition question thenBranch colon elseBranch } =
      resolveLocalExpression? table
        { span := otherSpan,
          value := .conditional condition otherQuestion thenBranch otherColon elseBranch } := by
  simp only [resolveLocalExpression?]

/-- Boolean negation ignores its operator range and the enclosing expression range. -/
theorem resolveLocalExpression?_logicalNot_spans (table : LocalNameTable) (operand : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand } =
      resolveLocalExpression? table
        { span := otherSpan, value := .unary ⟨otherOperatorSpan, .logicalNot⟩ operand } := by
  simp only [resolveLocalExpression?]

/-- Word complement ignores its operator range and the enclosing expression range. -/
theorem resolveLocalExpression?_bitNot_spans (table : LocalNameTable) (operand : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand } =
      resolveLocalExpression? table
        { span := otherSpan, value := .unary ⟨otherOperatorSpan, .bitNot⟩ operand } := by
  simp only [resolveLocalExpression?]

/-- Word addition keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_add_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .add⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .add⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word subtraction retains operand order and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_subtract_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .subtract⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .subtract⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word multiplication keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_multiply_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .multiply⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .multiply⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word division keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_divide_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .divide⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .divide⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word remainder keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_modulo_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .modulo⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .modulo⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Unsigned comparison retains operand order and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_greater_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .greater⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .greater⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word equality retains operand order and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_equal_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .equal⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .equal⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word inequality preserves its nested negation/equality tree and ignores only ranges. -/
theorem resolveLocalExpression?_notEqual_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .notEqual⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Unsigned less-or-equal retains the ordered comparison/negation tree and ignores ranges. -/
theorem resolveLocalExpression?_lessEqual_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .lessEqual⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Unsigned less-than retains both ordered operands and ignores only source ranges. -/
theorem resolveLocalExpression?_less_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .less⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .less⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Unsigned greater-or-equal retains the ordered less-than/negation tree and ignores ranges. -/
theorem resolveLocalExpression?_greaterEqual_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .greaterEqual⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word conjunction keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_bitAnd_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .bitAnd⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word disjunction keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_bitOr_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .bitOr⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Word exclusive-or keeps both operand trees and ignores only the operator/outer ranges. -/
theorem resolveLocalExpression?_bitXor_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .bitXor⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Conjunction's generated false constant is independent of its source ranges. -/
theorem resolveLocalExpression?_logicalAnd_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .logicalAnd⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Disjunction's generated true constant is independent of its source ranges. -/
theorem resolveLocalExpression?_logicalOr_spans (table : LocalNameTable) (left right : Syntax.Expr)
    (span operatorSpan otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right } =
      resolveLocalExpression? table
        { span := otherSpan, value := .binary left ⟨otherOperatorSpan, .logicalOr⟩ right } := by
  simp only [resolveLocalExpression?]

/-- Identifier spelling, not either occurrence range, selects the local ID. -/
theorem resolveLocalExpression?_identifier_value_eq (table : LocalNameTable)
    {left right : Syntax.Identifier} (same : left.value = right.value)
    (leftSpan rightSpan : Syntax.SourceSpan) :
    resolveLocalExpression? table { span := leftSpan, value := .identifier left } =
      resolveLocalExpression? table { span := rightSpan, value := .identifier right } := by
  simp only [resolveLocalExpression?, same]

theorem resolveLocalExpression?_group (table : LocalNameTable) (span : Syntax.SourceSpan)
    (inner : Syntax.Expr) :
    resolveLocalExpression? table { span, value := .group inner } = resolveLocalExpression? table inner := by
  simp only [resolveLocalExpression?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionResolutionProperties`
-/

/-! Exact structural resolution for the supported canonical expression fragment.
All written children must resolve, including short-circuit operands; branch
selection belongs to evaluation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.complete {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved) :
    resolveLocalExpression? table source = some resolved := by
  induction resolution with
  | unit => simp only [resolveLocalExpression?]
  | identifier found =>
      simp only [resolveLocalExpression?, LocalNameTable.lookup?_iff.mpr found, Option.map_some]
  | wordLiteral meaning =>
      simp only [resolveLocalExpression?, interpretWordLiteral?_complete meaning, Option.map_some]
  | group _ ih => simpa only [resolveLocalExpression?] using ih
  | pair _ _ leftIH rightIH => simp [resolveLocalExpression?, leftIH, rightIH]
  | many _ _ headIH tailIH =>
      rw [resolveLocalExpression?]
      simp only [headIH, tailIH, bind, pure, Option.bind_some]
  | logicalNot _ ih | bitNot _ ih => simp only [resolveLocalExpression?, ih, Option.map_some]
  | add _ _ leftIH rightIH | subtract _ _ leftIH rightIH | multiply _ _ leftIH rightIH
  | divide _ _ leftIH rightIH | modulo _ _ leftIH rightIH
  | greater _ _ leftIH rightIH | equal _ _ leftIH rightIH | notEqual _ _ leftIH rightIH
  | lessEqual _ _ leftIH rightIH | less _ _ leftIH rightIH
  | greaterEqual _ _ leftIH rightIH
  | bitAnd _ _ leftIH rightIH
  | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH
  | logicalAnd _ _ leftIH rightIH | logicalOr _ _ leftIH rightIH =>
      simp [resolveLocalExpression?, leftIH, rightIH]
  | conditional _ _ _ conditionIH thenIH elseIH =>
      simp [resolveLocalExpression?, conditionIH, thenIH, elseIH]

theorem resolveLocalExpression?_sound {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (result : resolveLocalExpression? table source = some resolved) :
    ResolvesLocalExpression table source resolved := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [resolveLocalExpression?, reduceCtorEq] at result
      case identifier name =>
        cases found : table.lookup? name.value with
        | none => simp only [found, Option.map_none, reduceCtorEq] at result
        | some id =>
            simp only [found, Option.map_some, Option.some.injEq] at result
            cases result
            exact .identifier (LocalNameTable.lookup?_iff.mp found)
      case literal literal =>
        simp only [Option.map_eq_some_iff] at result
        obtain ⟨word, interpreted, same⟩ := result
        cases same
        exact .wordLiteral (interpretWordLiteral?_sound interpreted)
      case group inner => exact .group (resolveLocalExpression?_sound result)
      case tuple elements =>
        cases elements with
        | mk tupleSpan elements =>
            cases elements with
            | nil =>
                simp only [resolveLocalExpression?, Option.some.injEq] at result
                cases result
                exact .unit
            | cons left rest =>
                cases rest with
                | nil => simp only [resolveLocalExpression?, reduceCtorEq] at result
                | cons right rest =>
                    cases rest with
                    | nil =>
                        simp only [resolveLocalExpression?, bind, Option.bind_eq_some_iff, pure] at result
                        obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
                        cases same
                        exact .pair (resolveLocalExpression?_sound leftResult)
                          (resolveLocalExpression?_sound rightResult)
                    | cons third rest =>
                        rw [resolveLocalExpression?] at result
                        simp only [bind, Option.bind_eq_some_iff, pure] at result
                        obtain ⟨resolvedHead, headResult, resolvedTail, tailResult, same⟩ := result
                        cases same
                        exact .many (resolveLocalExpression?_sound headResult)
                          (resolveLocalExpression?_sound tailResult)
      case unary operator operand =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue with
        | logicalNot =>
            simp only [resolveLocalExpression?, Option.map_eq_some_iff] at result
            obtain ⟨resolvedOperand, operandResult, same⟩ := result
            cases same
            exact .logicalNot (resolveLocalExpression?_sound operandResult)
        | bitNot =>
            simp only [resolveLocalExpression?, Option.map_eq_some_iff] at result
            obtain ⟨resolvedOperand, operandResult, same⟩ := result
            cases same
            exact .bitNot (resolveLocalExpression?_sound operandResult)
      case binary left operator right =>
        rcases operator with ⟨operatorSpan, operatorValue⟩
        cases operatorValue <;> try simp only [resolveLocalExpression?] at result
        case add =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .add (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case subtract =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .subtract (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case multiply =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .multiply (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case divide =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .divide (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case modulo =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .modulo (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case greater =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .greater (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case equal =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .equal (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case notEqual =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .notEqual (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case lessEqual =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .lessEqual (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case less =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .less (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case greaterEqual =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .greaterEqual (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case bitAnd =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .bitAnd (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case bitOr =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .bitOr (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case bitXor =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .bitXor (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case logicalAnd =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .logicalAnd (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
        case logicalOr =>
          simp only [bind, Option.bind_eq_some_iff, pure] at result
          obtain ⟨resolvedLeft, leftResult, resolvedRight, rightResult, same⟩ := result
          cases same
          exact .logicalOr (resolveLocalExpression?_sound leftResult)
            (resolveLocalExpression?_sound rightResult)
      case conditional condition question thenBranch colon elseBranch =>
        simp only [bind, Option.bind_eq_some_iff, pure] at result
        obtain ⟨resolvedCondition, conditionResult, resolvedThen, thenResult,
          resolvedElse, elseResult, same⟩ := result
        cases same
        exact .conditional (resolveLocalExpression?_sound conditionResult)
          (resolveLocalExpression?_sound thenResult) (resolveLocalExpression?_sound elseResult)
termination_by sizeOf source

theorem resolveLocalExpression?_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr} :
    resolveLocalExpression? table source = some resolved ↔
      ResolvesLocalExpression table source resolved :=
  ⟨resolveLocalExpression?_sound, ResolvesLocalExpression.complete⟩

theorem resolveLocalExpression?_eq_none_iff {table : LocalNameTable} {source : Syntax.Expr} :
    resolveLocalExpression? table source = none ↔
      ¬ ∃ resolved, ResolvesLocalExpression table source resolved := by
  constructor
  · intro result ⟨resolved, resolution⟩
    have accepted := resolution.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : resolveLocalExpression? table source with
    | none => rfl
    | some resolved => exact False.elim (absent ⟨resolved, resolveLocalExpression?_sound result⟩)

theorem ResolvesLocalExpression.deterministic {table : LocalNameTable}
    {source : Syntax.Expr} {left right : Resolved.Expr}
    (leftResolution : ResolvesLocalExpression table source left)
    (rightResolution : ResolvesLocalExpression table source right) : left = right :=
  Option.some.inj (leftResolution.complete.symm.trans rightResolution.complete)

/-- The established reference fragment embeds without changing its selected identity. -/
theorem ResolvesLocalReference.toLocalExpression {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id) :
    ResolvesLocalExpression table source (.var id) := by
  induction reference with
  | identifier found => exact .identifier found
  | group _ ih => exact .group ih

end Solcore.Frontend
