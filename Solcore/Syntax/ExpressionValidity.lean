import Solcore.Syntax.ParameterValidity
import Solcore.Syntax.Term

/-! Recursive source-validity contract for canonical Core expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace Block

/-- A Core block and every retained statement belong to one source. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (block : Block) : Prop :=
  block.span.ValidFor file ∧
    ∀ statement ∈ block.value, statementValid file statement

end Block

namespace Expr

/--
Every range recursively retained by an expression belongs to one source.
Lambda bodies use a supplied statement contract, keeping this layer usable
before the expression/statement recursion knot is closed.
-/
inductive ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) : Expr → Prop where
  | literal {span : SourceSpan} {literal : CoreLiteral}
      (spanValid : span.ValidFor file)
      (literalValid : literal.span.ValidFor file) :
      ValidFor statementValid file { span, value := .literal literal }
  | identifier {span : SourceSpan} {name : Identifier}
      (spanValid : span.ValidFor file)
      (nameValid : name.span.ValidFor file) :
      ValidFor statementValid file { span, value := .identifier name }
  | dotConstructor {span dot : SourceSpan} {name : Identifier}
      {arguments : Option (DelimitedList Expr)}
      (spanValid : span.ValidFor file) (dotValid : dot.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (argumentsSpanValid : ∀ values ∈ arguments,
        values.span.ValidFor file)
      (argumentsValid : ∀ values ∈ arguments,
        ∀ argument ∈ values.elements,
          ValidFor statementValid file argument) :
      ValidFor statementValid file {
        span
        value := .dotConstructor dot name arguments
      }
  | proxy {span marker : SourceSpan} {type : TypeExpr}
      (spanValid : span.ValidFor file) (markerValid : marker.ValidFor file)
      (typeValid : TypeExpr.ValidFor file type) :
      ValidFor statementValid file { span, value := .proxy marker type }
  | lambda {span keyword : SourceSpan}
      {parameters : DelimitedList LambdaParameter}
      {returnType : Option TypeExpr} {body : Block}
      (spanValid : span.ValidFor file) (keywordValid : keyword.ValidFor file)
      (parametersSpanValid : parameters.span.ValidFor file)
      (parametersValid : ∀ parameter ∈ parameters.elements,
        LambdaParameter.ValidFor file parameter)
      (returnTypeValid : ∀ type ∈ returnType, TypeExpr.ValidFor file type)
      (bodyValid : Block.ValidFor statementValid file body) :
      ValidFor statementValid file {
        span
        value := .lambda keyword parameters returnType body
      }
  | unary {span : SourceSpan} {operator : Located UnaryOp} {operand : Expr}
      (spanValid : span.ValidFor file)
      (operatorValid : operator.span.ValidFor file)
      (operandValid : ValidFor statementValid file operand) :
      ValidFor statementValid file { span, value := .unary operator operand }
  | binary {span : SourceSpan} {left right : Expr}
      {operator : Located BinaryOp}
      (spanValid : span.ValidFor file)
      (leftValid : ValidFor statementValid file left)
      (operatorValid : operator.span.ValidFor file)
      (rightValid : ValidFor statementValid file right) :
      ValidFor statementValid file {
        span
        value := .binary left operator right
      }
  | index {span brackets : SourceSpan} {base index : Expr}
      (spanValid : span.ValidFor file)
      (baseValid : ValidFor statementValid file base)
      (bracketsValid : brackets.ValidFor file)
      (indexValid : ValidFor statementValid file index) :
      ValidFor statementValid file { span, value := .index base brackets index }
  | call {span : SourceSpan} {callee : Expr}
      {arguments : DelimitedList Expr}
      (spanValid : span.ValidFor file)
      (calleeValid : ValidFor statementValid file callee)
      (argumentsSpanValid : arguments.span.ValidFor file)
      (argumentsValid : ∀ argument ∈ arguments.elements,
        ValidFor statementValid file argument) :
      ValidFor statementValid file { span, value := .call callee arguments }
  | field {span dot : SourceSpan} {base : Expr} {name : Identifier}
      (spanValid : span.ValidFor file)
      (baseValid : ValidFor statementValid file base)
      (dotValid : dot.ValidFor file) (nameValid : name.span.ValidFor file) :
      ValidFor statementValid file { span, value := .field base dot name }
  | conditional {span question colon : SourceSpan}
      {condition thenBranch elseBranch : Expr}
      (spanValid : span.ValidFor file)
      (conditionValid : ValidFor statementValid file condition)
      (questionValid : question.ValidFor file)
      (thenValid : ValidFor statementValid file thenBranch)
      (colonValid : colon.ValidFor file)
      (elseValid : ValidFor statementValid file elseBranch) :
      ValidFor statementValid file {
        span
        value := .conditional condition question thenBranch colon elseBranch
      }
  | group {span : SourceSpan} {inner : Expr}
      (spanValid : span.ValidFor file)
      (innerValid : ValidFor statementValid file inner) :
      ValidFor statementValid file { span, value := .group inner }
  | tuple {span : SourceSpan} {elements : DelimitedList Expr}
      (spanValid : span.ValidFor file)
      (elementsSpanValid : elements.span.ValidFor file)
      (elementsValid : ∀ element ∈ elements.elements,
        ValidFor statementValid file element) :
      ValidFor statementValid file { span, value := .tuple elements }
  | array {span : SourceSpan} {elements : DelimitedList Expr}
      (spanValid : span.ValidFor file)
      (elementsSpanValid : elements.span.ValidFor file)
      (elementsValid : ∀ element ∈ elements.elements,
        ValidFor statementValid file element) :
      ValidFor statementValid file { span, value := .array elements }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor statementValid file { span, value := .error }

/-- The outer range retained by every valid expression is source-valid. -/
theorem ValidFor.span_valid {statementValid : SourceFile → Statement → Prop}
    {file : SourceFile} {expression : Expr}
    (valid : ValidFor statementValid file expression) :
    expression.span.ValidFor file := by
  cases valid <;> assumption

end Expr

end Solcore.Syntax
