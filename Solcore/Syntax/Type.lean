import Solcore.Syntax.Foundation

set_option autoImplicit false

namespace Solcore.Syntax

/-- Source-preserving type-expression payload. -/
inductive TypeExprValue where
  | named
      (name : QualifiedName)
      (arguments : Option (NonemptyDelimitedList (Located TypeExprValue)))
  | mapping
      (keyword : SourceSpan)
      (argumentsSpan : SourceSpan)
      (key : Located TypeExprValue)
      (value : Located TypeExprValue)
  | proxy
      (marker : SourceSpan)
      (inner : Located TypeExprValue)
  | function
      (keyword : SourceSpan)
      (parameters : DelimitedList (Located TypeExprValue))
      (returns : Option (DelimitedList (Located TypeExprValue)))
  | comptime
      (keyword : SourceSpan)
      (argumentsSpan : SourceSpan)
      (inner : Located TypeExprValue)
  | tuple (elements : List (Located TypeExprValue))
  | error
  deriving Repr, BEq

/-- A complete type expression paired with its outer source range. -/
abbrev TypeExpr := Located TypeExprValue

/-- One trait predicate written `subject: Trait<arguments...>`. -/
structure Predicate where
  span : SourceSpan
  subject : TypeExpr
  traitName : Identifier
  arguments : Option (NonemptyDelimitedList TypeExpr)
  deriving Repr, BEq

/-- Nonempty generic parameter list written between angle brackets. -/
abbrev GenericParameters := NonemptyDelimitedList Identifier

/-- A named-function parameter, including parser recovery placeholders. -/
inductive FunctionParameterValue where
  | typed
      (comptime : Option SourceSpan)
      (name : Identifier)
      (type : TypeExpr)
  | error
  deriving Repr, BEq

abbrev FunctionParameter := Located FunctionParameterValue

/-- A lambda parameter, preserving whether its type was inferred. -/
inductive LambdaParameterValue where
  | inferred (name : Identifier)
  | typed
      (comptime : Option SourceSpan)
      (name : Identifier)
      (type : TypeExpr)
  | error
  deriving Repr, BEq

abbrev LambdaParameter := Located LambdaParameterValue

/-- Optional `where` clause with its nonempty predicate sequence. -/
structure WhereClause where
  span : SourceSpan
  predicates : NonemptyList Predicate
  deriving Repr, BEq

end Solcore.Syntax
