import Solcore.Surface.Token

set_option autoImplicit false

namespace Solcore.Surface

abbrev Name := Located String

inductive TypeSyntax where
  | unit (span : SourceSpan)
  | named (name : Name)
  deriving Repr, BEq, DecidableEq

namespace TypeSyntax

def span : TypeSyntax → SourceSpan
  | .unit sourceSpan => sourceSpan
  | .named name => name.span

def ValidFor (type : TypeSyntax) (file : SourceFile) : Prop :=
  type.span.ValidFor file

def spansValidFor (type : TypeSyntax) (file : SourceFile) : Bool :=
  type.span.isValidFor file

theorem spansValidFor_eq_true_iff (type : TypeSyntax) (file : SourceFile) :
    type.spansValidFor file = true ↔ type.ValidFor file := by
  simp [spansValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff]

end TypeSyntax

inductive IntegerBase where
  | decimal
  | hexadecimal
  deriving Repr, BEq, DecidableEq

structure IntegerLiteral where
  base : IntegerBase
  digits : String
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

inductive UnaryOp where
  | not
  deriving Repr, BEq, DecidableEq

inductive BinaryOp where
  | mul
  | div
  | mod
  | add
  | sub
  | bitAnd
  | bitXor
  | bitOr
  | lt
  | gt
  | le
  | ge
  | eq
  | ne
  deriving Repr, BEq, DecidableEq

inductive Expr where
  | unit (span : SourceSpan)
  | integer (literal : IntegerLiteral)
  | name (name : Name)
  | group (span : SourceSpan) (inner : Expr)
  | call (span : SourceSpan) (callee : Name) (arguments : List Expr)
  | unary (span : SourceSpan) (operator : Located UnaryOp) (operand : Expr)
  | binary
      (span : SourceSpan)
      (operator : Located BinaryOp)
      (left : Expr)
      (right : Expr)
  | ifThenElse
      (span : SourceSpan)
      (condition : Expr)
      (thenBranch : Expr)
      (elseBranch : Expr)
  deriving Repr, BEq

namespace Expr

def span : Expr → SourceSpan
  | .unit sourceSpan => sourceSpan
  | .integer literal => literal.span
  | .name identifier => identifier.span
  | .group sourceSpan _ => sourceSpan
  | .call sourceSpan _ _ => sourceSpan
  | .unary sourceSpan _ _ => sourceSpan
  | .binary sourceSpan _ _ _ => sourceSpan
  | .ifThenElse sourceSpan _ _ _ => sourceSpan

def allSpans : Expr → List SourceSpan
  | .unit sourceSpan =>
      [sourceSpan]
  | .integer literal =>
      [literal.span]
  | .name identifier =>
      [identifier.span]
  | .group sourceSpan inner =>
      sourceSpan :: inner.allSpans
  | .call sourceSpan callee arguments =>
      sourceSpan :: callee.span :: arguments.flatMap allSpans
  | .unary sourceSpan operator operand =>
      sourceSpan :: operator.span :: operand.allSpans
  | .binary sourceSpan operator left right =>
      sourceSpan :: operator.span :: left.allSpans ++ right.allSpans
  | .ifThenElse sourceSpan condition thenBranch elseBranch =>
      sourceSpan ::
        condition.allSpans ++ thenBranch.allSpans ++ elseBranch.allSpans
termination_by expression => sizeOf expression

def containments : Expr → List (SourceSpan × SourceSpan)
  | .unit _
  | .integer _
  | .name _ =>
      []
  | .group sourceSpan inner =>
      (sourceSpan, inner.span) :: inner.containments
  | .call sourceSpan callee arguments =>
      (sourceSpan, callee.span) ::
        arguments.map (fun argument => (sourceSpan, argument.span)) ++
          arguments.flatMap containments
  | .unary sourceSpan operator operand =>
      (sourceSpan, operator.span) ::
        (sourceSpan, operand.span) :: operand.containments
  | .binary sourceSpan operator left right =>
      (sourceSpan, operator.span) ::
        (sourceSpan, left.span) ::
        (sourceSpan, right.span) ::
        left.containments ++ right.containments
  | .ifThenElse sourceSpan condition thenBranch elseBranch =>
      (sourceSpan, condition.span) ::
        (sourceSpan, thenBranch.span) ::
        (sourceSpan, elseBranch.span) ::
        condition.containments ++ thenBranch.containments ++ elseBranch.containments
termination_by expression => sizeOf expression

def ValidFor (expression : Expr) (file : SourceFile) : Prop :=
  (∀ sourceSpan ∈ expression.allSpans, sourceSpan.ValidFor file) ∧
    ∀ containment ∈ expression.containments,
      containment.1.Contains containment.2

def spansValidFor (expression : Expr) (file : SourceFile) : Bool :=
  expression.allSpans.all (·.isValidFor file) &&
    expression.containments.all fun containment =>
      containment.1.contains containment.2

theorem spansValidFor_eq_true_iff (expression : Expr) (file : SourceFile) :
    expression.spansValidFor file = true ↔ expression.ValidFor file := by
  simp [spansValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff,
    SourceSpan.contains_eq_true_iff]

end Expr

structure LetStatement where
  span : SourceSpan
  name : Name
  type : TypeSyntax
  value : Expr
  deriving Repr, BEq

namespace LetStatement

def ValidFor (statement : LetStatement) (file : SourceFile) : Prop :=
  statement.span.ValidFor file ∧
    statement.name.span.ValidFor file ∧
    statement.span.Contains statement.name.span ∧
    statement.span.Contains statement.type.span ∧
    statement.span.Contains statement.value.span ∧
    statement.type.ValidFor file ∧
    statement.value.ValidFor file

def spansValidFor (statement : LetStatement) (file : SourceFile) : Bool :=
  statement.span.isValidFor file &&
    statement.name.span.isValidFor file &&
    statement.span.contains statement.name.span &&
    statement.span.contains statement.type.span &&
    statement.span.contains statement.value.span &&
    statement.type.spansValidFor file &&
    statement.value.spansValidFor file

theorem spansValidFor_eq_true_iff (statement : LetStatement) (file : SourceFile) :
    statement.spansValidFor file = true ↔ statement.ValidFor file := by
  simp [spansValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff,
    SourceSpan.contains_eq_true_iff, TypeSyntax.spansValidFor_eq_true_iff,
    Expr.spansValidFor_eq_true_iff, and_assoc]

end LetStatement

structure ReturnStatement where
  span : SourceSpan
  value : Expr
  deriving Repr, BEq

namespace ReturnStatement

def ValidFor (statement : ReturnStatement) (file : SourceFile) : Prop :=
  statement.span.ValidFor file ∧
    statement.span.Contains statement.value.span ∧
    statement.value.ValidFor file

def spansValidFor (statement : ReturnStatement) (file : SourceFile) : Bool :=
  statement.span.isValidFor file &&
    statement.span.contains statement.value.span &&
    statement.value.spansValidFor file

theorem spansValidFor_eq_true_iff (statement : ReturnStatement) (file : SourceFile) :
    statement.spansValidFor file = true ↔ statement.ValidFor file := by
  simp [spansValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff,
    SourceSpan.contains_eq_true_iff, Expr.spansValidFor_eq_true_iff, and_assoc]

end ReturnStatement

structure FunctionDecl where
  span : SourceSpan
  name : Name
  returnType : TypeSyntax
  bindings : List LetStatement
  result : ReturnStatement
  deriving Repr, BEq

namespace FunctionDecl

def ValidFor (declaration : FunctionDecl) (file : SourceFile) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.name.span.ValidFor file ∧
    declaration.span.Contains declaration.name.span ∧
    declaration.span.Contains declaration.returnType.span ∧
    declaration.returnType.ValidFor file ∧
    (∀ binding ∈ declaration.bindings,
      declaration.span.Contains binding.span ∧ binding.ValidFor file) ∧
    declaration.span.Contains declaration.result.span ∧
    declaration.result.ValidFor file

def spansValidFor (declaration : FunctionDecl) (file : SourceFile) : Bool :=
  declaration.span.isValidFor file &&
    declaration.name.span.isValidFor file &&
    declaration.span.contains declaration.name.span &&
    declaration.span.contains declaration.returnType.span &&
    declaration.returnType.spansValidFor file &&
    (declaration.bindings.all fun binding =>
      declaration.span.contains binding.span &&
        binding.spansValidFor file) &&
    declaration.span.contains declaration.result.span &&
    declaration.result.spansValidFor file

theorem spansValidFor_eq_true_iff (declaration : FunctionDecl) (file : SourceFile) :
    declaration.spansValidFor file = true ↔ declaration.ValidFor file := by
  simp [spansValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff,
    SourceSpan.contains_eq_true_iff, TypeSyntax.spansValidFor_eq_true_iff,
    LetStatement.spansValidFor_eq_true_iff, ReturnStatement.spansValidFor_eq_true_iff,
    and_assoc]

end FunctionDecl

structure ParsedFile where
  span : SourceSpan
  function : FunctionDecl
  comments : List Comment
  deriving Repr, BEq

namespace ParsedFile

def ValidFor (parsed : ParsedFile) (file : SourceFile) : Prop :=
  parsed.span.ValidFor file ∧
    parsed.span.Contains parsed.function.span ∧
    parsed.function.ValidFor file ∧
    ∀ comment ∈ parsed.comments, comment.ValidFor file

def spansValidFor (parsed : ParsedFile) (file : SourceFile) : Bool :=
  parsed.span.isValidFor file &&
    parsed.span.contains parsed.function.span &&
    parsed.function.spansValidFor file &&
    parsed.comments.all (·.isValidFor file)

theorem spansValidFor_eq_true_iff (parsed : ParsedFile) (file : SourceFile) :
    parsed.spansValidFor file = true ↔ parsed.ValidFor file := by
  simp [spansValidFor, ValidFor, SourceSpan.isValidFor_eq_true_iff,
    SourceSpan.contains_eq_true_iff, FunctionDecl.spansValidFor_eq_true_iff,
    Comment.isValidFor_eq_true_iff, and_assoc]

end ParsedFile

end Solcore.Surface
