import Solcore.Syntax.Foundation

/-!
Types and parameters: `TypeExpr`, `Predicate`, `WhereClause`, `GenericParameters`,
`FunctionParameter`, `LambdaParameter`.
-/

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
  /-- `T[]`, an array of `element`; `brackets` covers the `[` and the `]`. -/
  | array
      (element : Located TypeExprValue)
      (brackets : SourceSpan)
  | error
  deriving Repr, BEq

/-- A complete type expression paired with its outer source range. -/
abbrev TypeExpr := Located TypeExprValue

/-- `element[]`: its range runs from the element to the `]`, and its brackets
from the `[` to the `]`. -/
def TypeExpr.arrayOf (element : TypeExpr)
    (openingSpan closingSpan : SourceSpan) : TypeExpr := {
  span := SourceSpan.cover element.span closingSpan
  value := .array element (SourceSpan.cover openingSpan closingSpan)
}

/-- Whether a type is an array, `T[]`. -/
def TypeExpr.isArray (type : TypeExpr) : Bool :=
  match type.value with
  | .array _ _ => true
  | _ => false

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
