import Solcore.Syntax.Declaration
import Solcore.Syntax.ParameterValidity

/-! Source-validity contracts for predicates and callable signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace Predicate

/-- Every range retained by one trait predicate belongs to one source. -/
def ValidFor (file : SourceFile) (predicate : Predicate) : Prop :=
  predicate.span.ValidFor file ∧
    TypeExpr.ValidFor file predicate.subject ∧
    predicate.traitName.span.ValidFor file ∧
    (∀ arguments ∈ predicate.arguments, arguments.span.ValidFor file) ∧
    ∀ arguments ∈ predicate.arguments,
      ∀ argument ∈ arguments.elements.toList,
        TypeExpr.ValidFor file argument

end Predicate

namespace WhereClause

/-- A `where` range and all of its predicates belong to one source. -/
def ValidFor (file : SourceFile) (clause : WhereClause) : Prop :=
  clause.span.ValidFor file ∧
    ∀ predicate ∈ clause.predicates.toList,
      Predicate.ValidFor file predicate

end WhereClause

namespace FunctionModifiers

/-- Every written function-modifier marker belongs to one source. -/
def ValidFor (file : SourceFile) (modifiers : FunctionModifiers) : Prop :=
  (∀ marker ∈ modifiers.publicMarker, marker.ValidFor file) ∧
    ∀ marker ∈ modifiers.payableMarker, marker.ValidFor file

end FunctionModifiers

namespace ReturnClause

/-- A return clause and all retained result types belong to one source. -/
def ValidFor (file : SourceFile) (clause : ReturnClause) : Prop :=
  clause.span.ValidFor file ∧
    clause.types.span.ValidFor file ∧
    ∀ type ∈ clause.types.elements, TypeExpr.ValidFor file type

end ReturnClause

namespace FunctionSignature

/-- Every range retained by a complete function signature is source-valid. -/
def ValidFor (file : SourceFile) (signature : FunctionSignature) : Prop :=
  signature.span.ValidFor file ∧
    signature.name.span.ValidFor file ∧
    (∀ parameters ∈ signature.genericParameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ signature.genericParameters,
      ∀ parameter ∈ parameters.elements.toList,
        parameter.span.ValidFor file) ∧
    signature.parameters.span.ValidFor file ∧
    (∀ parameter ∈ signature.parameters.elements,
      FunctionParameter.ValidFor file parameter) ∧
    signature.modifiers.ValidFor file ∧
    (∀ clause ∈ signature.returnsClause,
      ReturnClause.ValidFor file clause) ∧
    ∀ clause ∈ signature.whereClause,
      WhereClause.ValidFor file clause

end FunctionSignature

end Solcore.Syntax
