import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Frontend.WordLiteral
import Solcore.Resolved.Eval
import Solcore.Resolved.Typing
import Solcore.Core.Safety
import Solcore.Core.Correspondence
import Solcore.Syntax.Term
import Solcore.Resolved.Internal.ScopeLaws
import Solcore.Resolved.Identity

/-!
# Local expressions

The canonical local expression fragment: syntax, names, typing, evaluation, renaming and safety.
-/

section
-- leanmerge: from Solcore.Frontend.LocalExpression
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
        case shiftLeft | shiftRight | uncheckedAdd | uncheckedSubtract | uncheckedMultiply =>
          simp at result
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
end

section
-- leanmerge: from Solcore.Frontend.LocalExpressionEvaluation
/-! Independent canonical evaluation for the local conditional/operator fragment.
Evaluation requires only the selected branch, not whole-expression resolution.
Short-circuit forms forward any selected right value at this raw boundary;
source typing separately requires both operands to be Boolean. Word arithmetic,
bitwise operations, unsigned comparisons, Word equality/inequality and tuple elements
evaluate left to right. Tuples retain arbitrary actual components in right-associated
pairs; an empty tuple denotes unit without any lookup.
Both stores are explicit even though every constructor is store-preserving. Strict Word literals
return their independently denoted value without consulting caller tables. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalExpressionEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | identifier {store : Core.Store} {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {id : Resolved.LocalId} {value : Core.Value}
      (named : LocalNameTable.Lookup table name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      LocalExpressionEvaluates table environment store
        { span, value := .identifier name } value store
  | wordLiteral {store : Core.Store} {span : Syntax.SourceSpan}
      {literal : Syntax.CoreLiteral} {word : Core.Word}
      (meaning : WordLiteralDenotes literal word) :
      LocalExpressionEvaluates table environment store
        { span, value := .literal literal } (.word word) store
  | group {initialStore finalStore : Core.Store} {span : Syntax.SourceSpan}
      {inner : Syntax.Expr} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore inner value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .group inner } value finalStore
  | unit {store : Core.Store} {span tupleSpan : Syntax.SourceSpan} :
      LocalExpressionEvaluates table environment store
        { span, value := .tuple ⟨tupleSpan, []⟩ } .unit store
  | pair {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Value}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left leftValue middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right rightValue finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .tuple ⟨tupleSpan, [left, right]⟩ } (.pair leftValue rightValue) finalStore
  | many {initialStore middleStore finalStore : Core.Store}
      {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headValue tailValue : Core.Value}
      (headEvaluation : LocalExpressionEvaluates table environment initialStore first headValue middleStore)
      (tailEvaluation : LocalExpressionEvaluates table environment middleStore
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailValue finalStore) :
      LocalExpressionEvaluates table environment initialStore
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ (.pair headValue tailValue) finalStore
  | logicalNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Bool}
      (child : LocalExpressionEvaluates table environment initialStore operand (.bool value) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand } (.bool (!value)) finalStore
  | bitNot {initialStore finalStore : Core.Store} {span operatorSpan : Syntax.SourceSpan}
      {operand : Syntax.Expr} {value : Core.Word}
      (child : LocalExpressionEvaluates table environment initialStore operand (.word value) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand } (.word value.bitNot) finalStore
  | add {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .add⟩ right }
        (.word (leftValue.add rightValue)) finalStore
  | subtract {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .subtract⟩ right }
        (.word (leftValue.sub rightValue)) finalStore
  | multiply {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .multiply⟩ right }
        (.word (leftValue.mul rightValue)) finalStore
  | divide {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .divide⟩ right }
        (.word (leftValue.udiv rightValue)) finalStore
  | modulo {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .modulo⟩ right }
        (.word (leftValue.umod rightValue)) finalStore
  | bitAnd {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right }
        (.word (leftValue.bitAnd rightValue)) finalStore
  | bitOr {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right }
        (.word (leftValue.bitOr rightValue)) finalStore
  | bitXor {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right }
        (.word (leftValue.bitXor rightValue)) finalStore
  | greater {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
        (.bool (decide (leftValue > rightValue))) finalStore
  | less {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .less⟩ right }
        (.bool (decide (leftValue < rightValue))) finalStore
  | equal {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
        (.bool (leftValue == rightValue)) finalStore
  | notEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
        (.bool (!(leftValue == rightValue))) finalStore
  | lessEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right }
        (.bool (!(decide (leftValue > rightValue)))) finalStore
  | greaterEqual {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftValue rightValue : Core.Word}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.word leftValue) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right (.word rightValue) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right }
        (.bool (!(decide (leftValue < rightValue)))) finalStore
  | andTrue {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool true) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right } value finalStore
  | andFalse {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool false) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right } (.bool false) finalStore
  | orTrue {initialStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool true) finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right } (.bool true) finalStore
  | orFalse {initialStore middleStore finalStore : Core.Store}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : Core.Value}
      (leftEvaluation : LocalExpressionEvaluates table environment initialStore left (.bool false) middleStore)
      (rightEvaluation : LocalExpressionEvaluates table environment middleStore right value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right } value finalStore
  | ifTrue {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment initialStore
        condition (.bool true) middleStore)
      (branchEvaluation : LocalExpressionEvaluates table environment middleStore
        thenBranch value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch } value finalStore
  | ifFalse {initialStore middleStore finalStore : Core.Store}
      {span question colon : Syntax.SourceSpan} {condition thenBranch elseBranch : Syntax.Expr}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment initialStore
        condition (.bool false) middleStore)
      (branchEvaluation : LocalExpressionEvaluates table environment middleStore
        elseBranch value finalStore) :
      LocalExpressionEvaluates table environment initialStore
        { span, value := .conditional condition question thenBranch colon elseBranch } value finalStore

theorem LocalExpressionEvaluates.store_eq {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | identifier => rfl
  | wordLiteral => rfl
  | unit => rfl
  | group _ ih | logicalNot _ ih | bitNot _ ih | andFalse _ ih | orTrue _ ih => exact ih
  | ifTrue _ _ conditionIH branchIH | ifFalse _ _ conditionIH branchIH =>
      exact branchIH.trans conditionIH
  | pair _ _ leftIH rightIH
  | many _ _ leftIH rightIH
  | add _ _ leftIH rightIH | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH
  | subtract _ _ leftIH rightIH | multiply _ _ leftIH rightIH | greater _ _ leftIH rightIH
  | divide _ _ leftIH rightIH | modulo _ _ leftIH rightIH
  | less _ _ leftIH rightIH
  | equal _ _ leftIH rightIH
  | notEqual _ _ leftIH rightIH
  | lessEqual _ _ leftIH rightIH
  | greaterEqual _ _ leftIH rightIH
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH =>
      exact rightIH.trans leftIH

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluation`
-/

/-! Determinism for independent source evaluation. The historical import path
continues to expose the evaluation rules and unchanged store law. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- No whole-resolution or typing premise is needed for source determinism. -/
theorem LocalExpressionEvaluates.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (leftEvaluation : LocalExpressionEvaluates table environment initialStore source left leftStore)
    (rightEvaluation : LocalExpressionEvaluates table environment initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction leftEvaluation generalizing right rightStore with
  | unit => cases rightEvaluation; exact ⟨rfl, rfl⟩
  | identifier named found =>
      cases rightEvaluation with
      | identifier otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound, rfl⟩
  | wordLiteral meaning =>
      cases rightEvaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl⟩
  | group _ ih =>
      cases rightEvaluation with
      | group child => exact ih child
  | pair _ _ leftIH rightIH =>
      cases rightEvaluation with
      | pair leftChild rightChild =>
          obtain ⟨rfl, rfl⟩ := leftIH leftChild
          obtain ⟨rfl, storeEq⟩ := rightIH rightChild
          exact ⟨rfl, storeEq⟩
  | many _ _ headIH tailIH =>
      cases rightEvaluation with
      | many headChild tailChild =>
          obtain ⟨rfl, rfl⟩ := headIH headChild
          obtain ⟨rfl, storeEq⟩ := tailIH tailChild
          exact ⟨rfl, storeEq⟩
  | logicalNot _ ih =>
      cases rightEvaluation with
      | logicalNot child =>
          obtain ⟨same, storeEq⟩ := ih child
          cases same
          exact ⟨rfl, storeEq⟩
  | bitNot _ ih =>
      cases rightEvaluation with
      | bitNot child =>
          obtain ⟨same, storeEq⟩ := ih child
          cases same
          exact ⟨rfl, storeEq⟩
  | add _ _ leftIH rightIH =>
      cases rightEvaluation with
      | add leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | subtract _ _ leftIH rightIH =>
      cases rightEvaluation with
      | subtract leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | multiply _ _ leftIH rightIH =>
      cases rightEvaluation with
      | multiply leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | divide _ _ leftIH rightIH =>
      cases rightEvaluation with
      | divide leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | modulo _ _ leftIH rightIH =>
      cases rightEvaluation with
      | modulo leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitAnd _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitAnd leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitOr _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitOr leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | bitXor _ _ leftIH rightIH =>
      cases rightEvaluation with
      | bitXor leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | greater _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greater leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | less _ _ leftIH rightIH =>
      cases rightEvaluation with
      | less leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | equal _ _ leftIH rightIH =>
      cases rightEvaluation with
      | equal leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | notEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | notEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | lessEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | lessEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | greaterEqual _ _ leftIH rightIH =>
      cases rightEvaluation with
      | greaterEqual leftChild rightChild =>
          obtain ⟨sameLeft, rfl⟩ := leftIH leftChild
          obtain ⟨sameRight, storeEq⟩ := rightIH rightChild
          cases sameLeft; cases sameRight
          exact ⟨rfl, storeEq⟩
  | andTrue _ _ leftIH rightIH =>
      cases rightEvaluation with
      | andTrue leftChild rightChild =>
          obtain ⟨_, rfl⟩ := leftIH leftChild
          exact rightIH rightChild
      | andFalse leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | andFalse _ leftIH =>
      cases rightEvaluation with
      | andFalse leftChild => exact leftIH leftChild
      | andTrue leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orTrue _ leftIH =>
      cases rightEvaluation with
      | orTrue leftChild => exact leftIH leftChild
      | orFalse leftChild _ =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | orFalse _ _ leftIH rightIH =>
      cases rightEvaluation with
      | orFalse leftChild rightChild =>
          obtain ⟨_, rfl⟩ := leftIH leftChild
          exact rightIH rightChild
      | orTrue leftChild =>
          obtain ⟨impossible, _⟩ := leftIH leftChild
          cases impossible
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue condition branch =>
          obtain ⟨_, rfl⟩ := conditionIH condition
          exact branchIH branch
      | ifFalse condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifFalse condition branch =>
          obtain ⟨_, rfl⟩ := conditionIH condition
          exact branchIH branch
      | ifTrue condition _ =>
          obtain ⟨impossible, _⟩ := conditionIH condition
          cases impossible

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionEvaluationProperties`
-/

/-! Exact canonical-to-resolved evaluation correspondence. Whole structural
resolution is explicit: a skipped branch can otherwise prevent elaboration. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.preserves_evaluation {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore) :
    Resolved.Evaluates environment initialStore resolved value finalStore := by
  induction resolution generalizing initialStore finalStore value with
  | unit => cases evaluation; exact .unit
  | identifier named =>
      cases evaluation with
      | identifier otherNamed found =>
          cases named.id_unique otherNamed
          exact .var found
  | wordLiteral meaning =>
      cases evaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact .word
  | group _ ih =>
      cases evaluation with
      | group child => exact ih child
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair leftChild rightChild => exact .pair (leftIH leftChild) (rightIH rightChild)
  | many _ _ headIH tailIH =>
      cases evaluation with
      | many headChild tailChild => exact .pair (headIH headChild) (tailIH tailChild)
  | logicalNot _ ih =>
      cases evaluation with
      | logicalNot child => exact .unary (ih child) rfl
  | bitNot _ ih =>
      cases evaluation with
      | bitNot child => exact .unary (ih child) rfl
  | add _ _ leftIH rightIH =>
      cases evaluation with
      | add leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | subtract _ _ leftIH rightIH =>
      cases evaluation with
      | subtract leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | multiply _ _ leftIH rightIH =>
      cases evaluation with
      | multiply leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | divide _ _ leftIH rightIH =>
      cases evaluation with
      | divide leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | modulo _ _ leftIH rightIH =>
      cases evaluation with
      | modulo leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitAnd _ _ leftIH rightIH =>
      cases evaluation with
      | bitAnd leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitOr _ _ leftIH rightIH =>
      cases evaluation with
      | bitOr leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitXor _ _ leftIH rightIH =>
      cases evaluation with
      | bitXor leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | greater _ _ leftIH rightIH =>
      cases evaluation with
      | greater leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | less _ _ leftIH rightIH =>
      cases evaluation with
      | less leftChild rightChild => exact .wordLt (leftIH leftChild) (rightIH rightChild)
  | equal _ _ leftIH rightIH =>
      cases evaluation with
      | equal leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | notEqual leftChild rightChild => exact .unary (.binary (leftIH leftChild) (rightIH rightChild) rfl) rfl
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | lessEqual leftChild rightChild => exact .unary (.binary (leftIH leftChild) (rightIH rightChild) rfl) rfl
  | greaterEqual _ _ leftIH rightIH =>
      cases evaluation with
      | greaterEqual leftChild rightChild => exact .unary (.wordLt (leftIH leftChild) (rightIH rightChild)) rfl
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | andTrue leftChild rightChild => exact .ifTrue (leftIH leftChild) (rightIH rightChild)
      | andFalse leftChild => exact .ifFalse (leftIH leftChild) .bool
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | orTrue leftChild => exact .ifTrue (leftIH leftChild) .bool
      | orFalse leftChild rightChild => exact .ifFalse (leftIH leftChild) (rightIH rightChild)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch => exact .ifTrue (conditionIH condition) (thenIH branch)
      | ifFalse condition branch => exact .ifFalse (conditionIH condition) (elseIH branch)

theorem ResolvesLocalExpression.reflects_evaluation {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value}
    (evaluation : Resolved.Evaluates environment initialStore resolved value finalStore) :
    LocalExpressionEvaluates table environment initialStore source value finalStore := by
  induction resolution generalizing initialStore finalStore value with
  | unit => cases evaluation; exact .unit
  | identifier named =>
      cases evaluation with
      | var found => exact .identifier named found
  | wordLiteral meaning =>
      cases evaluation with
      | word => exact .wordLiteral meaning
  | group _ ih => exact .group (ih evaluation)
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair leftChild rightChild => exact .pair (leftIH leftChild) (rightIH rightChild)
  | many _ _ headIH tailIH =>
      cases evaluation with
      | pair headChild tailChild => exact .many (headIH headChild) (tailIH tailChild)
  | logicalNot _ ih =>
      cases evaluation with
      | @unary _ _ _ _ _ operandValue _ child applied =>
          cases operandValue <;> simp only [Core.UnaryOp.apply, reduceCtorEq] at applied
          case bool decision =>
            cases applied
            exact .logicalNot (ih child)
  | bitNot _ ih =>
      cases evaluation with
      | @unary _ _ _ _ _ operandValue _ child applied =>
          cases operandValue <;> simp only [Core.UnaryOp.apply, reduceCtorEq] at applied
          case word value =>
            cases applied
            exact .bitNot (ih child)
  | add _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .add (leftIH leftChild) (rightIH rightChild)
  | subtract _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .subtract (leftIH leftChild) (rightIH rightChild)
  | multiply _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .multiply (leftIH leftChild) (rightIH rightChild)
  | divide _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .divide (leftIH leftChild) (rightIH rightChild)
  | modulo _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .modulo (leftIH leftChild) (rightIH rightChild)
  | bitAnd _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitAnd (leftIH leftChild) (rightIH rightChild)
  | bitOr _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitOr (leftIH leftChild) (rightIH rightChild)
  | bitXor _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitXor (leftIH leftChild) (rightIH rightChild)
  | greater _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .greater (leftIH leftChild) (rightIH rightChild)
  | less _ _ leftIH rightIH =>
      cases evaluation with
      | wordLt leftChild rightChild => exact .less (leftIH leftChild) (rightIH rightChild)
  | equal _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .equal (leftIH leftChild) (rightIH rightChild)
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary equality negated =>
          cases equality with
          | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
              cases leftValue <;> cases rightValue <;>
                simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
              case word.word leftWord rightWord =>
                cases applied
                cases negated
                exact .notEqual (leftIH leftChild) (rightIH rightChild)
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary comparison negated =>
          cases comparison with
          | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
              cases leftValue <;> cases rightValue <;>
                simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
              case word.word leftWord rightWord =>
                cases applied
                cases negated
                exact .lessEqual (leftIH leftChild) (rightIH rightChild)
  | greaterEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary comparison negated =>
          cases comparison with
          | wordLt leftChild rightChild =>
              cases negated
              exact .greaterEqual (leftIH leftChild) (rightIH rightChild)
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | ifTrue leftChild rightChild => exact .andTrue (leftIH leftChild) (rightIH rightChild)
      | ifFalse leftChild constant =>
          cases constant
          exact .andFalse (leftIH leftChild)
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | ifTrue leftChild constant =>
          cases constant
          exact .orTrue (leftIH leftChild)
      | ifFalse leftChild rightChild => exact .orFalse (leftIH leftChild) (rightIH rightChild)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch => exact .ifTrue (conditionIH condition) (thenIH branch)
      | ifFalse condition branch => exact .ifFalse (conditionIH condition) (elseIH branch)

theorem ResolvesLocalExpression.evaluates_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Resolved.Evaluates environment initialStore resolved value finalStore :=
  ⟨resolution.preserves_evaluation, resolution.reflects_evaluation⟩

/-- Exact Core correspondence for an explicitly resolved and lowered expression.
The lowering scope is the runtime identity order, not merely its length. -/
theorem ResolvesLocalExpression.core_evaluates_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {core : Core.Expr}
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore :=
  resolution.evaluates_iff.trans lowered.evaluates_iff

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalExpressionTyping
/-! Independent typing for the supported canonical local-expression fragment.
Logical negation and short-circuit operators require Boolean operands;
Word complement, arithmetic and bitwise operations require Word operands.
Unsigned Word comparisons and equality/inequality require two Words and return Bool.
Empty tuples have Unit type; other supported tuples have right-associated product types. Conditionals require a Boolean
condition and equally typed branches. Numeric literals use the explicit strict
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
  | unit {span tupleSpan : Syntax.SourceSpan} :
      LocalExpressionHasType table context { span, value := .tuple ⟨tupleSpan, []⟩ } .unit
  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      {leftType rightType : Core.Ty}
      (leftTyped : LocalExpressionHasType table context left leftType)
      (rightTyped : LocalExpressionHasType table context right rightType) :
      LocalExpressionHasType table context
        { span, value := .tuple ⟨tupleSpan, [left, right]⟩ } (.product leftType rightType)
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} {headType tailType : Core.Ty}
      (headTyped : LocalExpressionHasType table context first headType)
      (tailTyped : LocalExpressionHasType table context
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailType) :
      LocalExpressionHasType table context
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ (.product headType tailType)
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
  | divide {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .divide⟩ right } .word
  | modulo {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .modulo⟩ right } .word
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
  | lessEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right } .bool
  | less {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .less⟩ right } .bool
  | greaterEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftTyped : LocalExpressionHasType table context left .word)
      (rightTyped : LocalExpressionHasType table context right .word) :
      LocalExpressionHasType table context
        { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right } .bool
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

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionTypingResolution`
-/

/-! Independent source typing constructs its exact resolved expression and type.
Kept separate so the established typing-properties import remains within its size limit. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionHasType.resolves {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType table context source type) :
    ∃ resolved, ResolvesLocalExpression table source resolved ∧ Resolved.HasType context resolved type := by
  induction typing with
  | unit => exact ⟨.unit, .unit, .unit⟩
  | identifier named found => exact ⟨_, .identifier named, .var found⟩
  | wordLiteral meaning => exact ⟨_, .wordLiteral meaning, .word⟩
  | group _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := ih
      exact ⟨resolved, .group resolution, typed⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .pair leftResolved rightResolved, .pair leftTyped rightTyped⟩
  | many _ _ headIH tailIH =>
      obtain ⟨head, headResolved, headTyped⟩ := headIH
      obtain ⟨tail, tailResolved, tailTyped⟩ := tailIH
      exact ⟨_, .many headResolved tailResolved, .pair headTyped tailTyped⟩
  | logicalNot _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := ih
      exact ⟨_, .logicalNot resolution, .unary typed⟩
  | bitNot _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := ih
      exact ⟨_, .bitNot resolution, .unary typed⟩
  | add _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .add leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | subtract _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .subtract leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | multiply _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .multiply leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | divide _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .divide leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | modulo _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .modulo leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | greater _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .greater leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | equal _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .equal leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | notEqual _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .notEqual leftResolved rightResolved, .unary (.binary leftTyped rightTyped)⟩
  | lessEqual _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .lessEqual leftResolved rightResolved, .unary (.binary leftTyped rightTyped)⟩
  | less _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .less leftResolved rightResolved, .wordLt leftTyped rightTyped⟩
  | greaterEqual _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .greaterEqual leftResolved rightResolved, .unary (.wordLt leftTyped rightTyped)⟩
  | bitAnd _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .bitAnd leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | bitOr _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .bitOr leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | bitXor _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .bitXor leftResolved rightResolved, .binary leftTyped rightTyped⟩
  | logicalAnd _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .logicalAnd leftResolved rightResolved, .ifE leftTyped rightTyped .bool⟩
  | logicalOr _ _ leftIH rightIH =>
      obtain ⟨left, leftResolved, leftTyped⟩ := leftIH
      obtain ⟨right, rightResolved, rightTyped⟩ := rightIH
      exact ⟨_, .logicalOr leftResolved rightResolved, .ifE leftTyped .bool rightTyped⟩
  | conditional _ _ _ conditionIH thenIH elseIH =>
      obtain ⟨condition, conditionResolved, conditionTyped⟩ := conditionIH
      obtain ⟨thenBranch, thenResolved, thenTyped⟩ := thenIH
      obtain ⟨elseBranch, elseResolved, elseTyped⟩ := elseIH
      exact ⟨_, .conditional conditionResolved thenResolved elseResolved,
        .ifE conditionTyped thenTyped elseTyped⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionTypingProperties`
-/

/-! Independent canonical-fragment typing agrees exactly with resolved typing
and the executable Core checker. All conditional branches and short-circuit
operands are checked, even when dynamic evaluation would skip them. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.reflects_type {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (typing : Resolved.HasType context resolved type) :
    LocalExpressionHasType table context source type := by
  induction resolution generalizing type with
  | unit =>
      cases typing with
      | unit => exact .unit
  | identifier named =>
      cases typing with
      | var found => exact .identifier named found
  | wordLiteral meaning =>
      cases typing with
      | word => exact .wordLiteral meaning
  | group _ ih => exact .group (ih typing)
  | pair _ _ leftIH rightIH =>
      cases typing with
      | pair leftTyped rightTyped => exact .pair (leftIH leftTyped) (rightIH rightTyped)
  | many _ _ headIH tailIH =>
      cases typing with
      | pair headTyped tailTyped => exact .many (headIH headTyped) (tailIH tailTyped)
  | logicalNot _ ih =>
      cases typing with
      | unary operandTyped => exact .logicalNot (ih operandTyped)
  | bitNot _ ih =>
      cases typing with
      | unary operandTyped => exact .bitNot (ih operandTyped)
  | add _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .add (leftIH leftTyped) (rightIH rightTyped)
  | subtract _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .subtract (leftIH leftTyped) (rightIH rightTyped)
  | multiply _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .multiply (leftIH leftTyped) (rightIH rightTyped)
  | divide _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .divide (leftIH leftTyped) (rightIH rightTyped)
  | modulo _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .modulo (leftIH leftTyped) (rightIH rightTyped)
  | greater _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .greater (leftIH leftTyped) (rightIH rightTyped)
  | equal _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .equal (leftIH leftTyped) (rightIH rightTyped)
  | notEqual _ _ leftIH rightIH =>
      cases typing with
      | unary equalityTyped =>
          cases equalityTyped with
          | binary leftTyped rightTyped => exact .notEqual (leftIH leftTyped) (rightIH rightTyped)
  | lessEqual _ _ leftIH rightIH =>
      cases typing with
      | unary comparisonTyped =>
          cases comparisonTyped with
          | binary leftTyped rightTyped => exact .lessEqual (leftIH leftTyped) (rightIH rightTyped)
  | less _ _ leftIH rightIH =>
      cases typing with
      | wordLt leftTyped rightTyped => exact .less (leftIH leftTyped) (rightIH rightTyped)
  | greaterEqual _ _ leftIH rightIH =>
      cases typing with
      | unary comparisonTyped =>
          cases comparisonTyped with
          | wordLt leftTyped rightTyped => exact .greaterEqual (leftIH leftTyped) (rightIH rightTyped)
  | bitAnd _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .bitAnd (leftIH leftTyped) (rightIH rightTyped)
  | bitOr _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .bitOr (leftIH leftTyped) (rightIH rightTyped)
  | bitXor _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .bitXor (leftIH leftTyped) (rightIH rightTyped)
  | logicalAnd _ _ leftIH rightIH =>
      cases typing with
      | ifE leftTyped rightTyped falseTyped =>
          cases falseTyped
          exact .logicalAnd (leftIH leftTyped) (rightIH rightTyped)
  | logicalOr _ _ leftIH rightIH =>
      cases typing with
      | ifE leftTyped trueTyped rightTyped =>
          cases trueTyped
          exact .logicalOr (leftIH leftTyped) (rightIH rightTyped)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases typing with
      | ifE conditionTyped thenTyped elseTyped =>
          exact .conditional (conditionIH conditionTyped) (thenIH thenTyped) (elseIH elseTyped)

theorem ResolvesLocalExpression.preserves_type {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (typing : LocalExpressionHasType table context source type) :
    Resolved.HasType context resolved type := by
  obtain ⟨other, otherResolution, otherTyped⟩ := typing.resolves
  cases otherResolution.deterministic resolution
  exact otherTyped

theorem ResolvesLocalExpression.typing_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved) :
    LocalExpressionHasType table context source type ↔ Resolved.HasType context resolved type :=
  ⟨resolution.preserves_type, resolution.reflects_type⟩

theorem localExpressionHasType_iff_resolves {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType table context source type ↔
      ∃ resolved, ResolvesLocalExpression table source resolved ∧ Resolved.HasType context resolved type :=
  ⟨LocalExpressionHasType.resolves, fun ⟨_, resolution, typing⟩ => resolution.reflects_type typing⟩

/-- Every successful result retains its exact resolved expression, positional
Core expression, and independently assigned type. -/
theorem elaborateLocalExpression?_sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    ∃ resolved, ResolvesLocalExpression table source resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids context) resolved core ∧
      Resolved.HasType context resolved type := by
  simp only [elaborateLocalExpression?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨resolved, resolution, actualCore, lowering, actualType, inferred, result⟩ := accepted
  cases result
  have lowered := Resolved.Expr.lower?_sound lowering
  exact ⟨resolved, resolveLocalExpression?_sound resolution, lowered,
    lowered.reflects_type (Core.infer_sound inferred)⟩

theorem elaborateLocalExpression?_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolved core)
    (typing : Resolved.HasType context resolved type) :
    elaborateLocalExpression? table context source = some (core, type) := by
  simp [elaborateLocalExpression?, resolution.complete, lowered.complete,
    Core.infer_complete (lowered.preserves_type typing)]

theorem elaborateLocalExpression?_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalExpression? table context source = some (core, type) ↔
      ∃ resolved, ResolvesLocalExpression table source resolved ∧
        Resolved.Lowers (Resolved.LocalScope.ids context) resolved core ∧
        Resolved.HasType context resolved type :=
  ⟨elaborateLocalExpression?_sound,
    fun ⟨_, resolution, lowered, typing⟩ => elaborateLocalExpression?_complete resolution lowered typing⟩

theorem localExpressionHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType table context source type ↔
      ∃ core, elaborateLocalExpression? table context source = some (core, type) := by
  constructor
  · intro typing
    obtain ⟨resolved, resolution, resolvedTyped⟩ := typing.resolves
    obtain ⟨core, lowered, _⟩ := resolvedTyped.lowers
    exact ⟨core, elaborateLocalExpression?_complete resolution lowered resolvedTyped⟩
  · rintro ⟨core, accepted⟩
    obtain ⟨resolved, resolution, _, typing⟩ := elaborateLocalExpression?_sound accepted
    exact resolution.reflects_type typing

theorem elaborateLocalExpression?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  obtain ⟨resolved, _, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
  exact lowered.preserves_type typing

theorem LocalExpressionHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {left right : Core.Ty}
    (first : LocalExpressionHasType table context source left)
    (second : LocalExpressionHasType table context source right) : left = right := by
  obtain ⟨resolved, resolution, typed⟩ := first.resolves
  exact Resolved.typing_deterministic typed (resolution.preserves_type second)

theorem elaborateLocalExpression?_type_unique {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {leftCore rightCore : Core.Expr} {left right : Core.Ty}
    (first : elaborateLocalExpression? table context source = some (leftCore, left))
    (second : elaborateLocalExpression? table context source = some (rightCore, right)) : left = right :=
  (localExpressionHasType_iff_elaborates.mpr ⟨leftCore, first⟩).type_unique
    (localExpressionHasType_iff_elaborates.mpr ⟨rightCore, second⟩)

/-- Failure includes unsupported/unmapped syntax, missing local IDs, and
ill-typed operands or conditionals; none is promoted to whole-language rejection. -/
theorem elaborateLocalExpression?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} : elaborateLocalExpression? table context source = none ↔
      ¬ ∃ type, LocalExpressionHasType table context source type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := localExpressionHasType_iff_elaborates.mp typing
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalExpression? table context source with
    | none => rfl
    | some pair =>
        exact False.elim (missing ⟨pair.2, localExpressionHasType_iff_elaborates.mpr ⟨pair.1, result⟩⟩)

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalExpressionSafetyProperties
/-! Direct source-level existence and type/store preservation for the local
Unit/Boolean/Word/product/conditional fragment. Identity order and positional environment typing
remain explicit; no closedness or general resolved-evaluation existence theorem is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- An independently typed source expression evaluates in a matching typed
environment, returning a value of its assigned type and the unchanged store. -/
theorem LocalExpressionHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value, LocalExpressionEvaluates table environment store source value store ∧
      Core.ValueHasType value type := by
  induction typing with
  | unit => exact ⟨.unit, .unit, .unit⟩
  | identifier named found =>
      obtain ⟨index, indexed, atType⟩ := found.indexed
      obtain ⟨value, atValue, valueTyped⟩ := environmentTyped.lookup atType
      have envIndex := sameIds ▸ indexed
      exact ⟨value, .identifier named
        (Resolved.LocalScope.lookup_of_indexed envIndex atValue), valueTyped⟩
  | wordLiteral meaning => exact ⟨_, .wordLiteral meaning, .word⟩
  | group _ ih =>
      obtain ⟨value, evaluation, valueTyped⟩ := ih
      exact ⟨value, .group evaluation, valueTyped⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨left, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨right, rightEvaluation, rightTyped⟩ := rightIH
      exact ⟨.pair left right, .pair leftEvaluation rightEvaluation, .pair leftTyped rightTyped⟩
  | many _ _ headIH tailIH =>
      obtain ⟨head, headEvaluation, headTyped⟩ := headIH
      obtain ⟨tail, tailEvaluation, tailTyped⟩ := tailIH
      exact ⟨.pair head tail, .many headEvaluation tailEvaluation, .pair headTyped tailTyped⟩
  | logicalNot _ ih =>
      obtain ⟨value, evaluation, valueTyped⟩ := ih
      obtain ⟨decision, rfl⟩ := valueTyped.bool_shape
      exact ⟨.bool (!decision), .logicalNot evaluation, .bool⟩
  | bitNot _ ih =>
      obtain ⟨value, evaluation, valueTyped⟩ := ih
      cases valueTyped with
      | word => exact ⟨_, .bitNot evaluation, .word⟩
  | add _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .add leftEvaluation rightEvaluation, .word⟩
  | subtract _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .subtract leftEvaluation rightEvaluation, .word⟩
  | multiply _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .multiply leftEvaluation rightEvaluation, .word⟩
  | divide _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .divide leftEvaluation rightEvaluation, .word⟩
  | modulo _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .modulo leftEvaluation rightEvaluation, .word⟩
  | bitAnd _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .bitAnd leftEvaluation rightEvaluation, .word⟩
  | bitOr _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .bitOr leftEvaluation rightEvaluation, .word⟩
  | bitXor _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .bitXor leftEvaluation rightEvaluation, .word⟩
  | greater _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .greater leftEvaluation rightEvaluation, .bool⟩
  | less _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .less leftEvaluation rightEvaluation, .bool⟩
  | equal _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .equal leftEvaluation rightEvaluation, .bool⟩
  | notEqual _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .notEqual leftEvaluation rightEvaluation, .bool⟩
  | lessEqual _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .lessEqual leftEvaluation rightEvaluation, .bool⟩
  | greaterEqual _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
      cases leftTyped with
      | word =>
          cases rightTyped with
          | word => exact ⟨_, .greaterEqual leftEvaluation rightEvaluation, .bool⟩
  | logicalAnd _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨decision, rfl⟩ := leftTyped.bool_shape
      cases decision with
      | false => exact ⟨.bool false, .andFalse leftEvaluation, .bool⟩
      | true =>
          obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
          exact ⟨rightValue, .andTrue leftEvaluation rightEvaluation, rightTyped⟩
  | logicalOr _ _ leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftTyped⟩ := leftIH
      obtain ⟨decision, rfl⟩ := leftTyped.bool_shape
      cases decision with
      | false =>
          obtain ⟨rightValue, rightEvaluation, rightTyped⟩ := rightIH
          exact ⟨rightValue, .orFalse leftEvaluation rightEvaluation, rightTyped⟩
      | true => exact ⟨.bool true, .orTrue leftEvaluation, .bool⟩
  | conditional _ _ _ conditionIH thenIH elseIH =>
      obtain ⟨conditionValue, conditionEvaluation, conditionTyped⟩ := conditionIH
      obtain ⟨decision, rfl⟩ := conditionTyped.bool_shape
      cases decision with
      | false =>
          obtain ⟨value, evaluation, valueTyped⟩ := elseIH
          exact ⟨value, .ifFalse conditionEvaluation evaluation, valueTyped⟩
      | true =>
          obtain ⟨value, evaluation, valueTyped⟩ := thenIH
          exact ⟨value, .ifTrue conditionEvaluation evaluation, valueTyped⟩

/-- Every independent evaluation agrees with the typed result and exact store
endpoint, including open expressions and repeated caller-supplied identities. -/
theorem LocalExpressionEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty} {value : Core.Value}
    {initialStore finalStore : Core.Store}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore)
    (typing : LocalExpressionHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, valueTyped⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, storeEq⟩ := evaluation.deterministic evaluated
  exact ⟨valueTyped, storeEq⟩

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalExpressionExecutionProperties
/-! Checked canonical local expressions execute in an identity-aligned runtime
environment. Fuel exhaustion does not invalidate the source typing judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateLocalExpression?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  have environmentLowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core := by
    rw [sameIds]
    exact lowered
  exact resolution.core_evaluates_iff environmentLowered

theorem elaborateLocalExpression?_run_done_sound
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (result : Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
        .done value finalStore) :
    LocalExpressionEvaluates table environment initialStore source value finalStore ∧
      finalStore = initialStore := by
  have evaluation := (elaborateLocalExpression?_evaluates_iff accepted sameIds).mpr
    (Core.runStateful_evaluation_sound result)
  exact ⟨evaluation, evaluation.store_eq⟩

theorem elaborateLocalExpression?_evaluates_iff_run_done
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      ∃ fuel, Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) initialStore) =
          .done value finalStore := by
  constructor
  · intro evaluation
    obtain ⟨required, enough⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel
      ((elaborateLocalExpression?_evaluates_iff accepted sameIds).mp evaluation)
    exact ⟨required, enough required (Nat.le_refl _)⟩
  · rintro ⟨fuel, result⟩
    exact (elaborateLocalExpression?_run_done_sound accepted sameIds result).1

/-- Typed open local environments give existence, not only uniqueness, and
the exact source value is returned at every sufficiently large Core fuel. -/
theorem elaborateLocalExpression?_typed_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value required, LocalExpressionEvaluates table environment store source value store ∧
      Core.ValueHasType value type ∧
      ∀ fuel, required ≤ fuel → Core.runStateful fuel
        (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  have typing := localExpressionHasType_iff_elaborates.mpr ⟨core, accepted⟩
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates sameIds environmentTyped store
  obtain ⟨required, enough⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel
    ((elaborateLocalExpression?_evaluates_iff accepted sameIds).mp evaluation)
  exact ⟨value, required, evaluation, valueTyped, enough⟩

/-- Insufficient fuel cannot produce a machine fault for this checked pure
fragment. No runtime store-typing premise is needed for returning local values. -/
theorem elaborateLocalExpression?_run_never_faults
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) (fuel : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values environment) store) ≠
      .fault error faultState := by
  intro fault
  obtain ⟨value, required, _, _, enough⟩ :=
    elaborateLocalExpression?_typed_execution accepted sameIds environmentTyped store
  obtain ⟨steps, _, path, terminal⟩ := Core.runStateful_fault_sound fault
  have stillFault := Core.runStateful_fault_complete_of_steps path terminal
    (Nat.le_max_right required steps)
  have done := enough (max required steps) (Nat.le_max_left required steps)
  rw [done] at stillFault
  cases stillFault

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalName
/-! Local-name avoidance and renaming support. -/

/-!
## Consolidated module: `Solcore.Frontend.LocalNameAvoidance`
-/

/-! A spelling-avoidance condition for the local-expression shapes. Every literal
payload avoids all names, even if malformed, overflowing, or a string. This is
not a free-name analysis for other canonical syntax forms. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- No identifier in this expression has the specified spelling. Literal validity
is not required, since literal payloads do not perform name lookup.
All conditional children, binary operands and original tuple elements are checked, including
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
  | unit {span tupleSpan : Syntax.SourceSpan} :
      AvoidsLocalName name { span, value := .tuple ⟨tupleSpan, []⟩ }
  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .tuple ⟨tupleSpan, [left, right]⟩ }
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} (headAvoids : AvoidsLocalName name first)
      (tailAvoids : AvoidsLocalName name ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩) :
      AvoidsLocalName name ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
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
  | divide {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .divide⟩ right }
  | modulo {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .modulo⟩ right }
  | greater {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
  | equal {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
  | notEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
  | lessEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right }
  | less {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .less⟩ right }
  | greaterEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right }
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

/-!
## Consolidated module: `Solcore.Frontend.LocalNameAvoidanceProperties`
-/

/-! Adding an unused spelling preserves exact structural resolution. No
freshness of the supplied ID, table uniqueness, or successful resolution is
required; using the added spelling is deliberately outside these laws. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalNameTable.lookup_cons_iff_of_ne {table : LocalNameTable}
    {name spelling : String} {newId id : Resolved.LocalId} (different : name ≠ spelling) :
    LocalNameTable.Lookup ((name, newId) :: table) spelling id ↔
      LocalNameTable.Lookup table spelling id := by
  constructor
  · intro found
    cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => exact found
  · exact LocalNameTable.Lookup.tail different

theorem AvoidsLocalName.resolves_cons_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) {table : LocalNameTable}
    {id : Resolved.LocalId} {resolved : Resolved.Expr} :
    ResolvesLocalExpression ((name, id) :: table) source resolved ↔
      ResolvesLocalExpression table source resolved := by
  induction avoids generalizing resolved with
  | unit =>
      constructor <;> intro resolution <;> cases resolution <;> exact .unit
  | identifier different =>
      constructor
      · intro resolution
        cases resolution with
        | identifier found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mp found)
      · intro resolution
        cases resolution with
        | identifier found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr found)
  | literal =>
      constructor <;> intro resolution <;> cases resolution with
      | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih =>
      constructor
      · intro resolution
        cases resolution with
        | group child => exact .group (ih.mp child)
      · intro resolution
        cases resolution with
        | group child => exact .group (ih.mpr child)
  | pair _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | pair left right => exact .pair (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | pair left right => exact .pair (leftIH.mpr left) (rightIH.mpr right)
  | many _ _ headIH tailIH =>
      constructor
      · intro resolution
        cases resolution with
        | many head tail => exact .many (headIH.mp head) (tailIH.mp tail)
      · intro resolution
        cases resolution with
        | many head tail => exact .many (headIH.mpr head) (tailIH.mpr tail)
  | logicalNot _ ih =>
      constructor
      · intro resolution
        cases resolution with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro resolution
        cases resolution with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro resolution
        cases resolution with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro resolution
        cases resolution with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | divide _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | divide left right => exact .divide (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | divide left right => exact .divide (leftIH.mpr left) (rightIH.mpr right)
  | modulo _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | modulo left right => exact .modulo (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | modulo left right => exact .modulo (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | lessEqual _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | lessEqual left right => exact .lessEqual (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | lessEqual left right => exact .lessEqual (leftIH.mpr left) (rightIH.mpr right)
  | less _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | less left right => exact .less (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | less left right => exact .less (leftIH.mpr left) (rightIH.mpr right)
  | greaterEqual _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | greaterEqual left right => exact .greaterEqual (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | greaterEqual left right => exact .greaterEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | logicalAnd left right => exact .logicalAnd (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | logicalAnd left right => exact .logicalAnd (leftIH.mpr left) (rightIH.mpr right)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | logicalOr left right => exact .logicalOr (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | logicalOr left right => exact .logicalOr (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro resolution
        cases resolution with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mp condition) (thenIH.mp thenBranch) (elseIH.mp elseBranch)
      · intro resolution
        cases resolution with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mpr condition) (thenIH.mpr thenBranch) (elseIH.mpr elseBranch)

/-- Exact executable agreement includes unresolved expressions returning `none`. -/
theorem AvoidsLocalName.resolve_cons_eq {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (table : LocalNameTable) (id : Resolved.LocalId) :
    resolveLocalExpression? ((name, id) :: table) source = resolveLocalExpression? table source := by
  cases old : resolveLocalExpression? table source with
  | none =>
      cases extended : resolveLocalExpression? ((name, id) :: table) source with
      | none => rfl
      | some resolved =>
          have accepted := (avoids.resolves_cons_iff.mp (resolveLocalExpression?_sound extended)).complete
          rw [old] at accepted
          cases accepted
  | some resolved =>
      exact (avoids.resolves_cons_iff.mpr (resolveLocalExpression?_sound old)).complete

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalNameRenaming`
-/

/-! Relabel only the IDs in an explicit ordered name table. Spellings, row
order, and first-name-match behavior are unchanged, even for noninjective maps.
This is not source spelling renaming or a fresh-identity allocation policy. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalNameTable

def mapIds (mapping : Resolved.LocalId → Resolved.LocalId) (table : LocalNameTable) :
    LocalNameTable :=
  table.map (fun entry => (entry.1, mapping entry.2))

@[simp] theorem mapIds_id (table : LocalNameTable) : mapIds id table = table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, id⟩
      simp only [mapIds, List.map_cons] at ih ⊢
      exact congrArg (List.cons (name, id)) ih

theorem mapIds_comp (table : LocalNameTable)
    (first second : Resolved.LocalId → Resolved.LocalId) :
    mapIds second (mapIds first table) = mapIds (second ∘ first) table := by
  simp only [mapIds, List.map_map, Function.comp_def]

/-- Name lookup selects the same row; no injectivity premise is necessary. -/
theorem lookup?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (table : LocalNameTable) (spelling : String) :
    lookup? (mapIds mapping table) spelling = (lookup? table spelling).map mapping := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, id⟩
      by_cases same : candidate = spelling
      · simp only [mapIds, List.map_cons, lookup?, if_pos same, Option.map_some]
      · simpa only [mapIds, List.map_cons, lookup?, if_neg same] using ih

theorem lookup_mapIds_iff_exists (mapping : Resolved.LocalId → Resolved.LocalId)
    {table : LocalNameTable} {spelling : String} {renamed : Resolved.LocalId} :
    Lookup (mapIds mapping table) spelling renamed ↔
      ∃ original, Lookup table spelling original ∧ mapping original = renamed := by
  simp only [← lookup?_iff, lookup?_mapIds, Option.map_eq_some_iff]

theorem lookup_mapIds_iff (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping)
    {table : LocalNameTable} {spelling : String} {id : Resolved.LocalId} :
    Lookup (mapIds mapping table) spelling (mapping id) ↔ Lookup table spelling id := by
  rw [lookup_mapIds_iff_exists]
  constructor
  · rintro ⟨original, found, same⟩
    cases injective same
    exact found
  · intro found
    exact ⟨id, found, rfl⟩

end Solcore.Frontend.LocalNameTable
end

section
-- leanmerge: from Solcore.Frontend.LocalExpressionRenaming
/-! Local-expression renaming and its semantic correspondence. -/

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionRenamingProperties`
-/

/-! Resolution commutes with arbitrary identity maps. The source tree, including
all spellings and ranges, is unchanged. Unlike context/environment lookup,
name-based resolution does not require the map to be injective. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.mapIds {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (mapping : Resolved.LocalId → Resolved.LocalId) :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping table) source
      (resolved.renameIds mapping) := by
  induction resolution with
  | unit => exact .unit
  | identifier found =>
      exact .identifier ((LocalNameTable.lookup_mapIds_iff_exists mapping).mpr ⟨_, found, rfl⟩)
  | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih => exact .group ih
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | many _ _ headIH tailIH => exact .many headIH tailIH
  | logicalNot _ ih => exact .logicalNot ih
  | bitNot _ ih => exact .bitNot ih
  | add _ _ leftIH rightIH => exact .add leftIH rightIH
  | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
  | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
  | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
  | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
  | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
  | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
  | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
  | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
  | less _ _ leftIH rightIH => exact .less leftIH rightIH
  | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
  | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
  | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
  | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
  | logicalAnd _ _ leftIH rightIH => exact .logicalAnd leftIH rightIH
  | logicalOr _ _ leftIH rightIH => exact .logicalOr leftIH rightIH
  | conditional _ _ _ conditionIH thenIH elseIH => exact .conditional conditionIH thenIH elseIH

/-- Every renamed derivation has an original derivation, without choosing an
inverse map or assuming that distinct IDs remain distinct. -/
theorem resolvesLocalExpression_mapIds_iff_exists (mapping : Resolved.LocalId → Resolved.LocalId)
    {table : LocalNameTable} {source : Syntax.Expr} {renamed : Resolved.Expr} :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping table) source renamed ↔
      ∃ original, ResolvesLocalExpression table source original ∧
        original.renameIds mapping = renamed := by
  constructor
  · intro resolution
    induction resolution with
    | unit => exact ⟨.unit, .unit, rfl⟩
    | identifier found =>
        obtain ⟨original, originalFound, rfl⟩ :=
          (LocalNameTable.lookup_mapIds_iff_exists mapping).mp found
        exact ⟨.var original, .identifier originalFound, rfl⟩
    | wordLiteral meaning => exact ⟨_, .wordLiteral meaning, rfl⟩
    | group _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨original, .group child, rfl⟩
    | pair _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.pair originalLeft originalRight, .pair leftChild rightChild, rfl⟩
    | many _ _ headIH tailIH =>
        obtain ⟨originalHead, headChild, rfl⟩ := headIH
        obtain ⟨originalTail, tailChild, rfl⟩ := tailIH
        exact ⟨.pair originalHead originalTail, .many headChild tailChild, rfl⟩
    | logicalNot _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨.unary .boolNot original, .logicalNot child, rfl⟩
    | bitNot _ ih =>
        obtain ⟨original, child, rfl⟩ := ih
        exact ⟨.unary .wordNot original, .bitNot child, rfl⟩
    | add _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordAdd originalLeft originalRight, .add leftChild rightChild, rfl⟩
    | subtract _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordSub originalLeft originalRight, .subtract leftChild rightChild, rfl⟩
    | multiply _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordMul originalLeft originalRight, .multiply leftChild rightChild, rfl⟩
    | divide _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordDiv originalLeft originalRight, .divide leftChild rightChild, rfl⟩
    | modulo _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordMod originalLeft originalRight, .modulo leftChild rightChild, rfl⟩
    | greater _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordGt originalLeft originalRight, .greater leftChild rightChild, rfl⟩
    | equal _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordEq originalLeft originalRight, .equal leftChild rightChild, rfl⟩
    | notEqual _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordEq originalLeft originalRight), .notEqual leftChild rightChild, rfl⟩
    | lessEqual _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.unary .boolNot (.binary .wordGt originalLeft originalRight), .lessEqual leftChild rightChild, rfl⟩
    | less _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.wordLt originalLeft originalRight, .less leftChild rightChild, rfl⟩
    | greaterEqual _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.unary .boolNot (.wordLt originalLeft originalRight),
          .greaterEqual leftChild rightChild, rfl⟩
    | bitAnd _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordAnd originalLeft originalRight, .bitAnd leftChild rightChild, rfl⟩
    | bitOr _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordOr originalLeft originalRight, .bitOr leftChild rightChild, rfl⟩
    | bitXor _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.binary .wordXor originalLeft originalRight, .bitXor leftChild rightChild, rfl⟩
    | logicalAnd _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.ifE originalLeft originalRight (.bool false), .logicalAnd leftChild rightChild, rfl⟩
    | logicalOr _ _ leftIH rightIH =>
        obtain ⟨originalLeft, leftChild, rfl⟩ := leftIH
        obtain ⟨originalRight, rightChild, rfl⟩ := rightIH
        exact ⟨.ifE originalLeft (.bool true) originalRight, .logicalOr leftChild rightChild, rfl⟩
    | conditional _ _ _ conditionIH thenIH elseIH =>
        obtain ⟨originalCondition, conditionChild, rfl⟩ := conditionIH
        obtain ⟨originalThen, thenChild, rfl⟩ := thenIH
        obtain ⟨originalElse, elseChild, rfl⟩ := elseIH
        exact ⟨.ifE originalCondition originalThen originalElse,
          .conditional conditionChild thenChild elseChild, rfl⟩
  · rintro ⟨original, resolution, rfl⟩
    exact resolution.mapIds mapping

/-- Exact optional commutation includes all unsupported or unmapped source
trees; it does not silently assume whole-expression resolution succeeds. -/
theorem resolveLocalExpression?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (table : LocalNameTable) (source : Syntax.Expr) :
    resolveLocalExpression? (LocalNameTable.mapIds mapping table) source =
      (resolveLocalExpression? table source).map (Resolved.Expr.renameIds mapping) := by
  cases originalResult : resolveLocalExpression? table source with
  | none =>
      cases renamedResult : resolveLocalExpression? (LocalNameTable.mapIds mapping table) source with
      | none => rfl
      | some renamed =>
          obtain ⟨original, resolution, _⟩ :=
            (resolvesLocalExpression_mapIds_iff_exists mapping).mp
              (resolveLocalExpression?_sound renamedResult)
          have impossible := resolution.complete
          rw [originalResult] at impossible
          cases impossible
  | some original =>
      exact ((resolveLocalExpression?_sound originalResult).mapIds mapping).complete

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalExpressionRenamingSemantics`
-/

/-! Simultaneous injective relabeling preserves checking and raw evaluation
of the same source AST. Names, values, types, and both stores are unchanged;
no whole-resolution or typing premise is added to evaluation invariance. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Positional Core and its type are exactly unchanged, including failures. -/
theorem elaborateLocalExpression?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (table : LocalNameTable)
    (context : Resolved.Context) (source : Syntax.Expr) :
    elaborateLocalExpression? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source =
      elaborateLocalExpression? table context source := by
  cases resolved : resolveLocalExpression? table source with
  | none =>
      simp [elaborateLocalExpression?, resolveLocalExpression?_mapIds, resolved]
  | some expr =>
      simp [elaborateLocalExpression?, resolveLocalExpression?_mapIds, resolved,
        Resolved.Expr.lower?_renameIds mapping injective]

theorem localExpressionHasType_mapIds_iff (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping context) source type ↔
      LocalExpressionHasType table context source type := by
  rw [localExpressionHasType_iff_elaborates, localExpressionHasType_iff_elaborates]
  simp only [elaborateLocalExpression?_mapIds mapping injective]

/-- Raw evaluation preserves arbitrary selected right values and can skip
unresolved or unsupported syntax. No typing or whole-resolution assumption
is needed, even when the original tables repeat names or alias identities. -/
theorem localExpressionEvaluates_mapIds_iff (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {table : LocalNameTable}
    {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore ↔
      LocalExpressionEvaluates table environment initialStore source value finalStore := by
  constructor
  · intro evaluation
    induction evaluation with
    | unit => exact .unit
    | identifier named found =>
        obtain ⟨id, oldNamed, same⟩ := (LocalNameTable.lookup_mapIds_iff_exists mapping).mp named
        rw [← same] at found
        exact .identifier oldNamed ((Resolved.LocalScope.lookup_mapIds_iff mapping injective).mp found)
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
    | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
  · intro evaluation
    induction evaluation with
    | unit => exact .unit
    | identifier named found =>
        exact .identifier ((LocalNameTable.lookup_mapIds_iff mapping injective).mpr named)
          ((Resolved.LocalScope.lookup_mapIds_iff mapping injective).mpr found)
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
    | many _ _ headIH tailIH => exact .many headIH tailIH
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | divide _ _ leftIH rightIH => exact .divide leftIH rightIH
    | modulo _ _ leftIH rightIH => exact .modulo leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | less _ _ leftIH rightIH => exact .less leftIH rightIH
    | equal _ _ leftIH rightIH => exact .equal leftIH rightIH
    | notEqual _ _ leftIH rightIH => exact .notEqual leftIH rightIH
    | lessEqual _ _ leftIH rightIH => exact .lessEqual leftIH rightIH
    | greaterEqual _ _ leftIH rightIH => exact .greaterEqual leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalReferenceEmbeddingProperties
/-! The identifier/group adapter embeds exactly in the conditional adapter.
Variable-shaped resolution characterizes the old fragment; evaluating a
conditional to a local value does not turn it into an old reference expression. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A variable-shaped structural result can only arise from an old reference. -/
theorem ResolvesLocalExpression.toLocalReference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (resolution : ResolvesLocalExpression table source (.var id)) :
    ResolvesLocalReference table source id := by
  cases resolution with
  | identifier found => exact .identifier found
  | group child => exact .group child.toLocalReference
termination_by sizeOf source

theorem resolvesLocalExpression_var_iff_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId} :
    ResolvesLocalExpression table source (.var id) ↔ ResolvesLocalReference table source id :=
  ⟨ResolvesLocalExpression.toLocalReference, ResolvesLocalReference.toLocalExpression⟩

theorem resolveLocalExpression?_var_iff_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId} :
    resolveLocalExpression? table source = some (.var id) ↔
      resolveLocalReference? table source = some (.var id) :=
  resolveLocalExpression?_iff.trans
    (resolvesLocalExpression_var_iff_reference.trans resolveLocalReference?_iff.symm)

/-- Once the name resolves, both checked endpoints agree for every supplied
context, including contexts where the selected identity is absent. -/
theorem elaborateLocalExpression?_eq_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id) (context : Resolved.Context) :
    elaborateLocalExpression? table context source = elaborateLocalReference? table context source := by
  simp only [elaborateLocalExpression?, elaborateLocalReference?,
    reference.complete, reference.toLocalExpression.complete]

/-- On an already resolved reference, the new store-threaded evaluation is
exactly the old value judgment together with equality of the store endpoints. -/
theorem localExpressionEvaluates_iff_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      LocalReferenceEvaluates table environment source value ∧ finalStore = initialStore := by
  rw [reference.toLocalExpression.evaluates_iff]
  constructor
  · intro evaluation
    cases evaluation with
    | var found => exact ⟨.reference reference found, rfl⟩
  · rintro ⟨evaluation, rfl⟩
    cases evaluation with
    | reference actual found =>
        cases reference.id_unique actual
        exact .var found

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.LocalTypeInputs
/-! Ordered type-only local inputs share identities between name resolution
and typing. They contain neither runtime values nor inhabitation evidence. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure LocalTypeBinding where
  name : String
  id : Resolved.LocalId
  type : Core.Ty

structure LocalTypeInputs where
  bindings : List LocalTypeBinding
  ids_nodup : (bindings.map (·.id)).Nodup

namespace LocalTypeInputs

def ids (inputs : LocalTypeInputs) : List Resolved.LocalId :=
  inputs.bindings.map (·.id)

def names (inputs : LocalTypeInputs) : LocalNameTable :=
  inputs.bindings.map fun binding => (binding.name, binding.id)

def context (inputs : LocalTypeInputs) : Resolved.Context :=
  inputs.bindings.map fun binding => (binding.id, binding.type)

def empty : LocalTypeInputs := ⟨[], by simp⟩

/-- This explicit construction introduces no source-level binding policy. -/
def bindFresh (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) : LocalTypeInputs where
  bindings := { name, id := Resolved.freshLocalId owner inputs.ids, type } :: inputs.bindings
  ids_nodup := by
    change (Resolved.freshLocalId owner inputs.ids :: inputs.ids).Nodup
    exact List.nodup_cons.mpr
      ⟨Resolved.freshLocalId_not_mem owner inputs.ids, inputs.ids_nodup⟩

end LocalTypeInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalTypeInputsProperties`
-/

/-! Type-only inputs expose aligned static projections and fresh-binding laws,
without requiring or constructing a runtime environment. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalTypeInputs

@[simp] theorem context_ids (inputs : LocalTypeInputs) :
    Resolved.LocalScope.ids inputs.context = inputs.ids := by
  simp [context, ids, Resolved.LocalScope.ids, List.map_map]

@[simp] theorem names_ids (inputs : LocalTypeInputs) :
    inputs.names.map Prod.snd = inputs.ids := by
  simp only [names, ids, List.map_map, Function.comp_def]

@[simp] theorem empty_ids : empty.ids = [] := rfl

@[simp] theorem empty_names : empty.names = [] := rfl

@[simp] theorem empty_context : empty.context = [] := rfl

theorem bindFresh_bindings (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).bindings =
      { name, id := Resolved.freshLocalId owner inputs.ids, type } :: inputs.bindings := rfl

@[simp] theorem bindFresh_ids (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).ids =
      Resolved.freshLocalId owner inputs.ids :: inputs.ids := rfl

@[simp] theorem bindFresh_names (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).names =
      (name, Resolved.freshLocalId owner inputs.ids) :: inputs.names := rfl

@[simp] theorem bindFresh_context (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).context =
      (Resolved.freshLocalId owner inputs.ids, type) :: inputs.context := rfl

theorem bindFresh_id_fresh (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId) :
    Resolved.freshLocalId owner inputs.ids ∉ inputs.ids :=
  Resolved.freshLocalId_not_mem owner inputs.ids

end Solcore.Frontend.LocalTypeInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalTypeInputsRenaming`
-/

/-! Relabel explicit input identities without changing row order, spelling,
or type. Injectivity preserves the bundle's unique-ID invariant. -/

set_option autoImplicit false

namespace Solcore.Frontend

def LocalTypeBinding.mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (binding : LocalTypeBinding) : LocalTypeBinding :=
  { binding with id := mapping binding.id }

@[simp] theorem LocalTypeBinding.mapIds_id (binding : LocalTypeBinding) :
    binding.mapIds _root_.id = binding := by cases binding; rfl

theorem LocalTypeBinding.mapIds_comp (binding : LocalTypeBinding)
    (first second : Resolved.LocalId → Resolved.LocalId) :
    (binding.mapIds first).mapIds second = binding.mapIds (second ∘ first) := rfl

private theorem nodup_map_injective {α β : Type} (mapping : α → β)
    (injective : Function.Injective mapping) {values : List α} (distinct : values.Nodup) :
    (values.map mapping).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons value rest ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
        exact absent (injective same ▸ originalMember)
      · exact ih tailDistinct

namespace LocalTypeInputs

def mapIds (inputs : LocalTypeInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) : LocalTypeInputs where
  bindings := inputs.bindings.map (LocalTypeBinding.mapIds mapping)
  ids_nodup := by
    simpa [LocalTypeBinding.mapIds, List.map_map, Function.comp_def] using
      nodup_map_injective mapping injective inputs.ids_nodup

@[simp] theorem mapIds_bindings (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).bindings =
      inputs.bindings.map (LocalTypeBinding.mapIds mapping) := rfl

@[simp] theorem mapIds_ids (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).ids = inputs.ids.map mapping := by
  simp [ids, mapIds, LocalTypeBinding.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_names (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).names = LocalNameTable.mapIds mapping inputs.names := by
  simp [names, mapIds, LocalTypeBinding.mapIds, LocalNameTable.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_context (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).context = Resolved.LocalScope.mapIds mapping inputs.context := by
  simp [context, mapIds, LocalTypeBinding.mapIds, Resolved.LocalScope.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_id (inputs : LocalTypeInputs) :
    inputs.mapIds id (fun _ _ same => same) = inputs := by
  cases inputs
  simp [mapIds, show LocalTypeBinding.mapIds id = id from funext LocalTypeBinding.mapIds_id]

theorem mapIds_comp (inputs : LocalTypeInputs) (first second : Resolved.LocalId → Resolved.LocalId)
    (firstInjective : Function.Injective first) (secondInjective : Function.Injective second) :
    (inputs.mapIds first firstInjective).mapIds second secondInjective =
      inputs.mapIds (second ∘ first) (secondInjective.comp firstInjective) := by
  cases inputs
  simp [mapIds, List.map_map, Function.comp_def, LocalTypeBinding.mapIds_comp]

end LocalTypeInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalTypeInputsOwnerProperties`
-/

/-! Value-free fresh binding commutes with injective owner-only relabeling
for arbitrary input scopes, without an extra fresh-index assumption. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalTypeInputs

theorem bindFresh_mapOwner (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).bindFresh (mapping owner) name type := by
  have sameFresh : Resolved.freshLocalId (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids) := by
    rw [mapIds_ids]
    exact Resolved.freshLocalId_map_owner mapping injective owner inputs.ids
  cases inputs
  simp only [mapIds, bindFresh, List.map_cons, LocalTypeBinding.mapIds, LocalTypeInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

end Solcore.Frontend.LocalTypeInputs
end
