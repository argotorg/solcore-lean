import Solcore.Syntax.ValidityBasics
import Solcore.Syntax.Declaration
import Solcore.Syntax.Term
import Solcore.Syntax.Type
import Solcore.Syntax.Module
import Solcore.Syntax.Yul

/-!
Source validity of syntax: every span in a tree belongs to one file, in order.

Main declarations: `ParsedFile.ValidFor`, `TopItem.ValidFor`, `CoreStatement.ValidFor`,
`CoreExpr.ValidFor`, and the judgments for each declaration, such as
`FunctionDecl.ValidFor` and `ContractDecl.ValidFor`. The main theorems state their
provenance results with these.
-/

section
-- leanmerge: from Solcore.Syntax.DeriveValidity
/-! Source-validity contract for canonical derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeriveAttribute

/-- Every range retained by a derive attribute belongs to one source file. -/
def ValidFor (file : SourceFile) (value : DeriveAttribute) : Prop :=
  value.span.ValidFor file ∧
    value.value.targets.ValidFor QualifiedName.ValidFor file

end Solcore.Syntax.DeriveAttribute
end

section
-- leanmerge: from Solcore.Syntax.PatternValidity
/-! Recursive source-validity contract for canonical Core patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Pattern

/--
Every range recursively retained by a pattern belongs to one source.  The
contract for embedded comptime expressions is supplied by the expression
layer, so pattern provenance can be established independently.
-/
inductive ValidFor (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : Pattern → Prop where
  | wildcard {span marker : SourceSpan}
      (spanValid : span.ValidFor file)
      (markerValid : marker.ValidFor file) :
      ValidFor expressionValid file { span, value := .wildcard marker }
  | literal {span : SourceSpan} {literal : CoreLiteral}
      (spanValid : span.ValidFor file)
      (literalValid : literal.span.ValidFor file) :
      ValidFor expressionValid file { span, value := .literal literal }
  | binder {span : SourceSpan} {name : Identifier}
      (spanValid : span.ValidFor file)
      (nameValid : name.span.ValidFor file) :
      ValidFor expressionValid file { span, value := .binder name }
  | constructor {span : SourceSpan} {leadingDot : Option SourceSpan}
      {qualifiers : List Identifier} {name : Identifier}
      {arguments : Option (NonemptyDelimitedList Pattern)}
      (spanValid : span.ValidFor file)
      (leadingDotValid : ∀ marker ∈ leadingDot, marker.ValidFor file)
      (qualifiersValid : ∀ qualifier ∈ qualifiers,
        qualifier.span.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (argumentsSpanValid : ∀ values ∈ arguments,
        values.span.ValidFor file)
      (argumentsValid : ∀ values ∈ arguments,
        ∀ pattern ∈ values.elements.toList,
          ValidFor expressionValid file pattern) :
      ValidFor expressionValid file {
        span
        value := .constructor leadingDot qualifiers name arguments
      }
  | comptime {span keyword : SourceSpan} {expression : Expr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (expressionIsValid : expressionValid file expression) :
      ValidFor expressionValid file {
        span
        value := .comptime keyword expression
      }
  | group {span : SourceSpan} {inner : Pattern}
      (spanValid : span.ValidFor file)
      (innerValid : ValidFor expressionValid file inner) :
      ValidFor expressionValid file { span, value := .group inner }
  | tuple {span : SourceSpan} {elements : DelimitedList Pattern}
      (spanValid : span.ValidFor file)
      (elementsSpanValid : elements.span.ValidFor file)
      (elementsValid : ∀ element ∈ elements.elements,
        ValidFor expressionValid file element) :
      ValidFor expressionValid file { span, value := .tuple elements }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor expressionValid file { span, value := .error }

/-- The outer range retained by every valid pattern is source-valid. -/
theorem ValidFor.span_valid {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {pattern : Pattern}
    (valid : ValidFor expressionValid file pattern) :
    pattern.span.ValidFor file := by
  cases valid <;> assumption

end Solcore.Syntax.Pattern
end

section
-- leanmerge: from Solcore.Syntax.TypeValidity
/-! Source-validity contract for recursive canonical type expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace TypeExpr

/--
A recursive type expression is valid when its outer range and every range
retained by its payload belong to the same source file.
-/
inductive ValidFor (file : SourceFile) : TypeExpr → Prop where
  | namedWithoutArguments {span : SourceSpan} {name : QualifiedName}
      (spanValid : span.ValidFor file)
      (nameValid : QualifiedName.ValidFor file name) :
      ValidFor file { span, value := .named name none }
  | namedWithArguments {span : SourceSpan} {name : QualifiedName}
      {arguments : NonemptyDelimitedList TypeExpr}
      (spanValid : span.ValidFor file)
      (nameValid : QualifiedName.ValidFor file name)
      (argumentsSpanValid : arguments.span.ValidFor file)
      (argumentsValid : ∀ argument ∈ arguments.elements.toList,
        ValidFor file argument) :
      ValidFor file { span, value := .named name (some arguments) }
  | mapping {span keyword argumentsSpan : SourceSpan}
      {key value : TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (argumentsSpanValid : argumentsSpan.ValidFor file)
      (keyValid : ValidFor file key)
      (valueValid : ValidFor file value) :
      ValidFor file {
        span
        value := .mapping keyword argumentsSpan key value
      }
  | proxy {span marker : SourceSpan} {inner : TypeExpr}
      (spanValid : span.ValidFor file)
      (markerValid : marker.ValidFor file)
      (innerValid : ValidFor file inner) :
      ValidFor file { span, value := .proxy marker inner }
  | functionWithoutReturns {span keyword : SourceSpan}
      {parameters : DelimitedList TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (parametersSpanValid : parameters.span.ValidFor file)
      (parametersValid : ∀ parameter ∈ parameters.elements,
        ValidFor file parameter) :
      ValidFor file {
        span
        value := .function keyword parameters none
      }
  | functionWithReturns {span keyword : SourceSpan}
      {parameters returns : DelimitedList TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (parametersSpanValid : parameters.span.ValidFor file)
      (parametersValid : ∀ parameter ∈ parameters.elements,
        ValidFor file parameter)
      (returnsSpanValid : returns.span.ValidFor file)
      (returnsValid : ∀ result ∈ returns.elements,
        ValidFor file result) :
      ValidFor file {
        span
        value := .function keyword parameters (some returns)
      }
  | comptime {span keyword argumentsSpan : SourceSpan}
      {inner : TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (argumentsSpanValid : argumentsSpan.ValidFor file)
      (innerValid : ValidFor file inner) :
      ValidFor file {
        span
        value := .comptime keyword argumentsSpan inner
      }
  | tuple {span : SourceSpan} {elements : List TypeExpr}
      (spanValid : span.ValidFor file)
      (elementsValid : ∀ element ∈ elements, ValidFor file element) :
      ValidFor file { span, value := .tuple elements }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor file { span, value := .error }

/-- The outer range retained by every valid type expression is source-valid. -/
theorem ValidFor.span_valid {file : SourceFile} {value : TypeExpr}
    (valid : ValidFor file value) : value.span.ValidFor file := by
  cases valid <;> assumption

end TypeExpr

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.TypeDeclarationValidity
/-! Source-validity contracts for canonical type and enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace TypeAliasDecl

/-- Every range retained by a type alias belongs to one source. -/
def ValidFor (file : SourceFile) (declaration : TypeAliasDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    (∀ parameters ∈ declaration.value.parameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.parameters,
      ∀ parameter ∈ parameters.elements,
        parameter.span.ValidFor file) ∧
    TypeExpr.ValidFor file declaration.value.value

end TypeAliasDecl

namespace EnumConstructor

/-- Every comment, name, and field range retained by an enum case is valid. -/
def ValidFor (file : SourceFile) (constructor : EnumConstructor) : Prop :=
  constructor.span.ValidFor file ∧
    (∀ comment ∈ constructor.value.leadingComments,
      comment.span.ValidFor file) ∧
    constructor.value.name.span.ValidFor file ∧
    (∀ fields ∈ constructor.value.fields, fields.span.ValidFor file) ∧
    ∀ fields ∈ constructor.value.fields,
      ∀ field ∈ fields.elements, TypeExpr.ValidFor file field

end EnumConstructor

namespace EnumDecl

/-- Every range retained by a complete enum declaration is source-valid. -/
def ValidFor (file : SourceFile) (declaration : EnumDecl) : Prop :=
  declaration.span.ValidFor file ∧
    (∀ retained ∈ declaration.value.deriveAttribute,
      DeriveAttribute.ValidFor file retained) ∧
    declaration.value.name.span.ValidFor file ∧
    (∀ parameters ∈ declaration.value.parameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.parameters,
      ∀ parameter ∈ parameters.elements.toList,
        parameter.span.ValidFor file) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ constructor ∈ declaration.value.constructors,
      EnumConstructor.ValidFor file constructor

end EnumDecl

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.ParameterValidity
/-! Source-validity contracts for canonical function and lambda parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace FunctionParameter

/-- Every range retained by a named-function parameter belongs to one source. -/
inductive ValidFor (file : SourceFile) : FunctionParameter → Prop where
  | typed {span : SourceSpan} {comptime : Option SourceSpan}
      {name : Identifier} {type : TypeExpr}
      (spanValid : span.ValidFor file)
      (comptimeValid : ∀ marker ∈ comptime, marker.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (typeValid : TypeExpr.ValidFor file type) :
      ValidFor file { span, value := .typed comptime name type }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor file { span, value := .error }

/-- A valid function parameter has a valid outer range. -/
theorem ValidFor.span_valid {file : SourceFile} {parameter : FunctionParameter}
    (valid : ValidFor file parameter) : parameter.span.ValidFor file := by
  cases valid <;> assumption

end FunctionParameter

namespace LambdaParameter

/-- Every range retained by a lambda parameter belongs to one source. -/
inductive ValidFor (file : SourceFile) : LambdaParameter → Prop where
  | inferred {span : SourceSpan} {name : Identifier}
      (spanValid : span.ValidFor file)
      (nameValid : name.span.ValidFor file) :
      ValidFor file { span, value := .inferred name }
  | typed {span : SourceSpan} {comptime : Option SourceSpan}
      {name : Identifier} {type : TypeExpr}
      (spanValid : span.ValidFor file)
      (comptimeValid : ∀ marker ∈ comptime, marker.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (typeValid : TypeExpr.ValidFor file type) :
      ValidFor file { span, value := .typed comptime name type }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor file { span, value := .error }

/-- A valid lambda parameter has a valid outer range. -/
theorem ValidFor.span_valid {file : SourceFile} {parameter : LambdaParameter}
    (valid : ValidFor file parameter) : parameter.span.ValidFor file := by
  cases valid <;> assumption

end LambdaParameter

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.SignatureValidity
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
end

section
-- leanmerge: from Solcore.Syntax.CallableDeclarationValidity
/-! Source-validity contracts for functions, traits, and implementations. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace FunctionDecl

/-- Every signature and body range retained by a function is source-valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : FunctionDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.signature.ValidFor file ∧
    declaration.value.body.span.ValidFor file ∧
    ∀ statement ∈ declaration.value.body.value,
      statementValid file statement

end FunctionDecl

namespace TraitMethod

/-- Every comment, signature, and terminator retained by a trait method is valid. -/
def ValidFor (file : SourceFile) (method : TraitMethod) : Prop :=
  method.span.ValidFor file ∧
    (∀ comment ∈ method.value.leadingComments,
      comment.span.ValidFor file) ∧
    method.value.signature.ValidFor file ∧
    method.value.semicolon.ValidFor file

end TraitMethod

namespace TraitDecl

/-- Every range retained by a complete trait declaration is source-valid. -/
def ValidFor (file : SourceFile) (declaration : TraitDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    declaration.value.genericParameters.span.ValidFor file ∧
    (∀ parameter ∈ declaration.value.genericParameters.elements.toList,
      parameter.span.ValidFor file) ∧
    (∀ clause ∈ declaration.value.whereClause,
      WhereClause.ValidFor file clause) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ method ∈ declaration.value.methods,
      TraitMethod.ValidFor file method

end TraitDecl

namespace ImplMethod

/-- An implementation method retains valid comments and a valid function. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (method : ImplMethod) : Prop :=
  method.span.ValidFor file ∧
    (∀ comment ∈ method.value.leadingComments,
      comment.span.ValidFor file) ∧
    FunctionDecl.ValidFor statementValid file method.value.declaration

end ImplMethod

namespace ImplDecl

/-- Every range retained by a complete implementation declaration is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : ImplDecl) : Prop :=
  declaration.span.ValidFor file ∧
    (∀ marker ∈ declaration.value.defaultMarker, marker.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      ∀ parameter ∈ parameters.elements.toList,
        parameter.span.ValidFor file) ∧
    declaration.value.traitName.span.ValidFor file ∧
    declaration.value.headArguments.span.ValidFor file ∧
    (∀ argument ∈ declaration.value.headArguments.elements.toList,
      TypeExpr.ValidFor file argument) ∧
    (∀ clause ∈ declaration.value.whereClause,
      WhereClause.ValidFor file clause) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ method ∈ declaration.value.methods,
      ImplMethod.ValidFor statementValid file method

end ImplDecl

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.ContractDeclarationValidity
/-! Source-validity contracts for canonical contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace ContractField

/-- A contract field retains valid name, type, and initializer ranges. -/
def ValidFor (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (field : ContractField) : Prop :=
  field.span.ValidFor file ∧
    field.value.name.span.ValidFor file ∧
    TypeExpr.ValidFor file field.value.type ∧
    ∀ initializer ∈ field.value.initializer,
      expressionValid file initializer

end ContractField

namespace ConstructorDecl

/-- Every parameter, modifier, and body range in a constructor is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : ConstructorDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.parameters.span.ValidFor file ∧
    (∀ parameter ∈ declaration.value.parameters.elements,
      FunctionParameter.ValidFor file parameter) ∧
    (∀ marker ∈ declaration.value.payableMarker, marker.ValidFor file) ∧
    declaration.value.body.span.ValidFor file ∧
    ∀ statement ∈ declaration.value.body.value,
      statementValid file statement

end ConstructorDecl

namespace FallbackDecl

/-- Every parameter, modifier, and body range in a fallback is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (declaration : FallbackDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.parameters.span.ValidFor file ∧
    (∀ parameter ∈ declaration.value.parameters.elements,
      FunctionParameter.ValidFor file parameter) ∧
    (∀ marker ∈ declaration.value.payableMarker, marker.ValidFor file) ∧
    declaration.value.body.span.ValidFor file ∧
    ∀ statement ∈ declaration.value.body.value,
      statementValid file statement

end FallbackDecl

namespace ContractMember

/-- Every range retained by one contract member belongs to one source. -/
inductive ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : ContractMember → Prop where
  | field {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ContractField}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ContractField.ValidFor expressionValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .field declaration
      }
  | function {span : SourceSpan} {leadingComments : List Comment}
      {declaration : FunctionDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : FunctionDecl.ValidFor statementValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .function declaration
      }
  | constructor {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ConstructorDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ConstructorDecl.ValidFor statementValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .constructor declaration
      }
  | fallback {span : SourceSpan} {leadingComments : List Comment}
      {declaration : FallbackDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : FallbackDecl.ValidFor statementValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .fallback declaration
      }
  | typeAlias {span : SourceSpan} {leadingComments : List Comment}
      {declaration : TypeAliasDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : TypeAliasDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .typeAlias declaration
      }
  | enum {span : SourceSpan} {leadingComments : List Comment}
      {declaration : EnumDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : EnumDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .enum declaration
      }
  | error {span : SourceSpan} {leadingComments : List Comment}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .error
      }

end ContractMember

namespace ContractDecl

/-- Every range retained by a complete contract declaration is valid. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (declaration : ContractDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      parameters.span.ValidFor file) ∧
    (∀ parameters ∈ declaration.value.genericParameters,
      ∀ parameter ∈ parameters.elements.toList,
        parameter.span.ValidFor file) ∧
    declaration.value.bodySpan.ValidFor file ∧
    ∀ member ∈ declaration.value.members,
      ContractMember.ValidFor statementValid expressionValid file member

end ContractDecl

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.FileValidity
/-! Source-validity contracts for canonical top-level items and parsed files. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace TopItem

/-- Every range retained by one top-level item belongs to one source. -/
inductive ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : TopItem → Prop where
  | importDecl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ImportDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ImportDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .importDecl declaration
      }
  | exportDecl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ExportDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ExportDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .exportDecl declaration
      }
  | pragmaDecl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : PragmaDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : PragmaDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .pragmaDecl declaration
      }
  | typeAlias {span : SourceSpan} {leadingComments : List Comment}
      {declaration : TypeAliasDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : TypeAliasDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .typeAlias declaration
      }
  | enum {span : SourceSpan} {leadingComments : List Comment}
      {declaration : EnumDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : EnumDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .enum declaration
      }
  | trait {span : SourceSpan} {leadingComments : List Comment}
      {declaration : TraitDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : TraitDecl.ValidFor file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .trait declaration
      }
  | impl {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ImplDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ImplDecl.ValidFor statementValid file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .impl declaration
      }
  | contract {span : SourceSpan} {leadingComments : List Comment}
      {declaration : ContractDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : ContractDecl.ValidFor statementValid
        expressionValid file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .contract declaration
      }
  | function {span : SourceSpan} {leadingComments : List Comment}
      {declaration : FunctionDecl}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file)
      (declarationValid : FunctionDecl.ValidFor statementValid
        file declaration) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .function declaration
      }
  | error {span : SourceSpan} {leadingComments : List Comment}
      (spanValid : span.ValidFor file)
      (commentsValid : ∀ comment ∈ leadingComments,
        comment.span.ValidFor file) :
      ValidFor statementValid expressionValid file {
        span, leadingComments, value := .error
      }

/-- A valid top-level item has a valid outer range. -/
theorem ValidFor.span_valid
    {statementValid : SourceFile → Statement → Prop}
    {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {item : TopItem}
    (valid : ValidFor statementValid expressionValid file item) :
    item.span.ValidFor file := by
  cases valid <;> assumption

/-- A valid top-level item retains only valid leading comments. -/
theorem ValidFor.comments_valid
    {statementValid : SourceFile → Statement → Prop}
    {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {item : TopItem}
    (valid : ValidFor statementValid expressionValid file item) :
    ∀ comment ∈ item.leadingComments, comment.span.ValidFor file := by
  cases valid <;> assumption

end TopItem

namespace ParsedFile

/-- A parsed file is owned by, and retains only ranges from, one source. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (parsed : ParsedFile) : Prop :=
  parsed.source = file.id ∧
    parsed.span.ValidFor file ∧
    (∀ item ∈ parsed.items,
      TopItem.ValidFor statementValid expressionValid file item) ∧
    ∀ comment ∈ parsed.comments, comment.span.ValidFor file

end ParsedFile

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.ExpressionValidity
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
end

section
-- leanmerge: from Solcore.Syntax.StatementValidity
/-! Recursive source-validity contracts for canonical Core statements. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace ForItem

/-- Every range retained by one canonical `for` header item is valid. -/
inductive ValidFor (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : ForItem → Prop where
  | letDecl {span : SourceSpan} {name : Identifier}
      {type : Option TypeExpr} {initializer : Option Expr}
      (spanValid : span.ValidFor file) (nameValid : name.span.ValidFor file)
      (typeValid : ∀ value ∈ type, TypeExpr.ValidFor file value)
      (initializerValid : ∀ value ∈ initializer, expressionValid file value) :
      ValidFor expressionValid file {
        span
        value := .letDecl name type initializer
      }
  | expression {span : SourceSpan} {expression : Expr}
      (spanValid : span.ValidFor file)
      (expressionIsValid : expressionValid file expression) :
      ValidFor expressionValid file { span, value := .expression expression }
  | assignValue {span : SourceSpan} {target value : Expr}
      {operator : Located ValueAssignOp}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.span.ValidFor file)
      (valueValid : expressionValid file value) :
      ValidFor expressionValid file {
        span
        value := .assignValue target operator value
      }
  | assignBitNot {span operator : SourceSpan} {target : Expr}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.ValidFor file) :
      ValidFor expressionValid file {
        span
        value := .assignBitNot target operator
      }

/-- A valid `for` item has a valid outer range. -/
theorem ValidFor.span_valid {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {item : ForItem}
    (valid : ValidFor expressionValid file item) : item.span.ValidFor file := by
  cases valid <;> assumption

end ForItem

mutual

/-- Every range recursively retained by a Core statement is valid. -/
inductive Statement.ValidFor
    (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) : Statement → Prop where
  | letDecl {span : SourceSpan} {name : Identifier}
      {type : Option TypeExpr} {initializer : Option Expr}
      (spanValid : span.ValidFor file) (nameValid : name.span.ValidFor file)
      (typeValid : ∀ value ∈ type, TypeExpr.ValidFor file value)
      (initializerValid : ∀ value ∈ initializer, expressionValid file value) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .letDecl name type initializer
      }
  | returnStmt {span : SourceSpan} {value : Option Expr}
      (spanValid : span.ValidFor file)
      (valueValid : ∀ expression ∈ value, expressionValid file expression) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .returnStmt value
      }
  | expression {span : SourceSpan} {expression : Expr}
      {trailingSemicolon : Bool}
      (spanValid : span.ValidFor file)
      (expressionIsValid : expressionValid file expression) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .expression expression trailingSemicolon
      }
  | assignValue {span : SourceSpan} {target value : Expr}
      {operator : Located ValueAssignOp}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.span.ValidFor file)
      (valueValid : expressionValid file value) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .assignValue target operator value
      }
  | assignBitNot {span operator : SourceSpan} {target : Expr}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .assignBitNot target operator
      }
  | matchWith {span : SourceSpan}
      {scrutinees : NonemptyDelimitedList Expr} {arms : MatchArms}
      (spanValid : span.ValidFor file)
      (scrutineesSpanValid : scrutinees.span.ValidFor file)
      (scrutineesValid : ∀ expression ∈ scrutinees.elements.toList,
        expressionValid file expression)
      (armsValid : MatchArms.ValidFor expressionValid patternValid
        yulValid file arms) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .matchWith scrutinees arms
      }
  | forLoop {span headerSpan : SourceSpan}
      {initializer post : List ForItem} {condition : Expr} {body : Block}
      (spanValid : span.ValidFor file)
      (headerValid : headerSpan.ValidFor file)
      (initializerValid : ∀ item ∈ initializer,
        ForItem.ValidFor expressionValid file item)
      (conditionValid : expressionValid file condition)
      (postValid : ∀ item ∈ post,
        ForItem.ValidFor expressionValid file item)
      (bodySpanValid : body.span.ValidFor file)
      (bodyValid : ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .forLoop headerSpan initializer condition post body
      }
  | whileLoop {span : SourceSpan} {condition : Expr} {body : Block}
      (spanValid : span.ValidFor file)
      (conditionValid : expressionValid file condition)
      (bodySpanValid : body.span.ValidFor file)
      (bodyValid : ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .whileLoop condition body
      }
  | ifThen {span : SourceSpan} {condition : Expr} {thenBody : Block}
      {elseBody : Option Block}
      (spanValid : span.ValidFor file)
      (conditionValid : expressionValid file condition)
      (thenSpanValid : thenBody.span.ValidFor file)
      (thenValid : ∀ statement ∈ thenBody.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement)
      (elseSpanValid : ∀ body ∈ elseBody, body.span.ValidFor file)
      (elseValid : ∀ body ∈ elseBody, ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .ifThen condition thenBody elseBody
      }
  | block {span : SourceSpan} {body : List Statement}
      (spanValid : span.ValidFor file)
      (bodyValid : ∀ statement ∈ body,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .block body
      }
  | assembly {span : SourceSpan} {body : List YulStmt}
      (spanValid : span.ValidFor file)
      (bodyValid : ∀ statement ∈ body, yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .assembly body
      }
  | breakStmt {span : SourceSpan} (spanValid : span.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .breakStmt
      }
  | continueStmt {span : SourceSpan} (spanValid : span.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .continueStmt
      }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .error
      }

/-- Every range retained by a non-default match arm is valid. -/
inductive MatchCase.ValidFor
    (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) : MatchCase → Prop where
  | arm {span : SourceSpan} {pattern : Pattern} {body : Block}
      (spanValid : span.ValidFor file)
      (patternIsValid : patternValid file pattern)
      (bodySpanValid : body.span.ValidFor file)
      (bodyValid : ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      MatchCase.ValidFor expressionValid patternValid yulValid file {
        span
        value := { pattern, body }
      }

/-- Every range retained by a complete match-arm collection is valid. -/
inductive MatchArms.ValidFor
    (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) : MatchArms → Prop where
  | arms {span : SourceSpan} {cases : List MatchCase}
      {defaultBody : Option Block}
      (spanValid : span.ValidFor file)
      (casesValid : ∀ case ∈ cases,
        MatchCase.ValidFor expressionValid patternValid yulValid file case)
      (defaultSpanValid : ∀ body ∈ defaultBody, body.span.ValidFor file)
      (defaultValid : ∀ body ∈ defaultBody, ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      MatchArms.ValidFor expressionValid patternValid yulValid file {
        span
        value := { cases, defaultBody }
      }

end

namespace Statement.ValidFor

/-- A valid statement has a valid outer range. -/
theorem span_valid {expressionValid : SourceFile → Expr → Prop}
    {patternValid : SourceFile → Pattern → Prop}
    {yulValid : SourceFile → YulStmt → Prop}
    {file : SourceFile} {statement : Statement}
    (valid : Statement.ValidFor expressionValid patternValid yulValid
      file statement) : statement.span.ValidFor file := by
  cases valid <;> assumption

end Statement.ValidFor

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.CoreTermValidity
/-! Canonical recursive source-validity for Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace Expr.ValidFor

/-- Expression validity is monotone in its statement contract. -/
theorem mono {old new : SourceFile → Statement → Prop}
    (lift : ∀ {file statement}, old file statement → new file statement)
    {file : SourceFile} {expression : Expr}
    (valid : Expr.ValidFor old file expression) :
    Expr.ValidFor new file expression := by
  induction valid with
  | literal spanValid literalValid => exact .literal spanValid literalValid
  | identifier spanValid nameValid => exact .identifier spanValid nameValid
  | dotConstructor spanValid dotValid nameValid argumentsSpanValid
      argumentsValid argumentsInduction =>
      exact .dotConstructor spanValid dotValid nameValid argumentsSpanValid
        argumentsInduction
  | proxy spanValid markerValid typeValid =>
      exact .proxy spanValid markerValid typeValid
  | lambda spanValid keywordValid parametersSpanValid parametersValid
      returnTypeValid bodyValid =>
      exact .lambda spanValid keywordValid parametersSpanValid parametersValid
        returnTypeValid ⟨bodyValid.1, fun statement member =>
          lift (bodyValid.2 statement member)⟩
  | unary spanValid operatorValid _ operandInduction =>
      exact .unary spanValid operatorValid operandInduction
  | binary spanValid _ operatorValid _ leftInduction rightInduction =>
      exact .binary spanValid leftInduction operatorValid rightInduction
  | index spanValid _ bracketsValid _ baseInduction indexInduction =>
      exact .index spanValid baseInduction bracketsValid indexInduction
  | call spanValid _ argumentsSpanValid _ calleeInduction
      argumentsInduction =>
      exact .call spanValid calleeInduction argumentsSpanValid
        argumentsInduction
  | field spanValid _ dotValid nameValid baseInduction =>
      exact .field spanValid baseInduction dotValid nameValid
  | conditional spanValid _ questionValid _ colonValid _ conditionInduction
      thenInduction elseInduction =>
      exact .conditional spanValid conditionInduction questionValid
        thenInduction colonValid elseInduction
  | group spanValid _ innerInduction =>
      exact .group spanValid innerInduction
  | tuple spanValid elementsSpanValid _ elementsInduction =>
      exact .tuple spanValid elementsSpanValid elementsInduction
  | array spanValid elementsSpanValid _ elementsInduction =>
      exact .array spanValid elementsSpanValid elementsInduction
  | error spanValid => exact .error spanValid

end Expr.ValidFor

namespace Pattern.ValidFor

/-- Pattern validity is monotone in its embedded-expression contract. -/
theorem mono {old new : SourceFile → Expr → Prop}
    (lift : ∀ {file expression}, old file expression → new file expression)
    {file : SourceFile} {pattern : Pattern}
    (valid : Pattern.ValidFor old file pattern) :
    Pattern.ValidFor new file pattern := by
  induction valid with
  | wildcard spanValid markerValid => exact .wildcard spanValid markerValid
  | literal spanValid literalValid => exact .literal spanValid literalValid
  | binder spanValid nameValid => exact .binder spanValid nameValid
  | constructor spanValid leadingDotValid qualifiersValid nameValid
      argumentsSpanValid _ argumentsInduction =>
      exact .constructor spanValid leadingDotValid qualifiersValid nameValid
        argumentsSpanValid argumentsInduction
  | comptime spanValid keywordValid expressionValid =>
      exact .comptime spanValid keywordValid (lift expressionValid)
  | group spanValid _ innerInduction => exact .group spanValid innerInduction
  | tuple spanValid elementsSpanValid _ elementsInduction =>
      exact .tuple spanValid elementsSpanValid elementsInduction
  | error spanValid => exact .error spanValid

end Pattern.ValidFor

namespace ForItem.ValidFor

/-- `for`-item validity is monotone in its expression contract. -/
theorem mono {old new : SourceFile → Expr → Prop}
    (lift : ∀ {file expression}, old file expression → new file expression)
    {file : SourceFile} {item : ForItem}
    (valid : ForItem.ValidFor old file item) : ForItem.ValidFor new file item := by
  cases valid with
  | letDecl spanValid nameValid typeValid initializerValid =>
      exact .letDecl spanValid nameValid typeValid fun expression member =>
        lift (initializerValid expression member)
  | expression spanValid expressionValid =>
      exact .expression spanValid (lift expressionValid)
  | assignValue spanValid targetValid operatorValid valueValid =>
      exact .assignValue spanValid (lift targetValid) operatorValid
        (lift valueValid)
  | assignBitNot spanValid targetValid operatorValid =>
      exact .assignBitNot spanValid (lift targetValid) operatorValid

end ForItem.ValidFor

/-- Statement validity is monotone in all three embedded syntax contracts. -/
theorem Statement.ValidFor.mono {oldExpr newExpr : SourceFile → Expr → Prop}
    {oldPattern newPattern : SourceFile → Pattern → Prop}
    {oldYul newYul : SourceFile → YulStmt → Prop}
    (liftExpr : ∀ {file expression}, oldExpr file expression →
      newExpr file expression)
    (liftPattern : ∀ {file pattern}, oldPattern file pattern →
      newPattern file pattern)
    (liftYul : ∀ {file statement}, oldYul file statement →
      newYul file statement)
    {file : SourceFile} {statement : Statement}
    (valid : Statement.ValidFor oldExpr oldPattern oldYul file statement) :
    Statement.ValidFor newExpr newPattern newYul file statement := by
  exact Statement.ValidFor.rec
    (motive_1 := fun statement _ =>
      Statement.ValidFor newExpr newPattern newYul file statement)
    (motive_2 := fun matchCase _ =>
      MatchCase.ValidFor newExpr newPattern newYul file matchCase)
    (motive_3 := fun arms _ =>
      MatchArms.ValidFor newExpr newPattern newYul file arms)
    (fun spanValid nameValid typeValid initializerValid =>
      .letDecl spanValid nameValid typeValid fun expression member =>
        liftExpr (initializerValid expression member))
    (fun spanValid valueValid =>
      .returnStmt spanValid fun expression member =>
        liftExpr (valueValid expression member))
    (fun spanValid expressionValid =>
      .expression spanValid (liftExpr expressionValid))
    (fun spanValid targetValid operatorValid valueValid =>
      .assignValue spanValid (liftExpr targetValid) operatorValid
        (liftExpr valueValid))
    (fun spanValid targetValid operatorValid =>
      .assignBitNot spanValid (liftExpr targetValid) operatorValid)
    (fun spanValid scrutineesSpanValid scrutineesValid _ armsInduction =>
      .matchWith spanValid scrutineesSpanValid
        (fun expression member => liftExpr
          (scrutineesValid expression member)) armsInduction)
    (fun spanValid headerValid initializerValid conditionValid postValid
        bodySpanValid _ bodyInduction =>
      .forLoop spanValid headerValid
        (fun item member => (initializerValid item member).mono liftExpr)
        (liftExpr conditionValid)
        (fun item member => (postValid item member).mono liftExpr)
        bodySpanValid bodyInduction)
    (fun spanValid conditionValid bodySpanValid _ bodyInduction =>
      .whileLoop spanValid (liftExpr conditionValid) bodySpanValid
        bodyInduction)
    (fun spanValid conditionValid thenSpanValid _ elseSpanValid _
        thenInduction elseInduction =>
      .ifThen spanValid (liftExpr conditionValid) thenSpanValid
        thenInduction elseSpanValid elseInduction)
    (fun spanValid _ bodyInduction => .block spanValid bodyInduction)
    (fun spanValid bodyValid =>
      .assembly spanValid fun statement member =>
        liftYul (bodyValid statement member))
    (fun spanValid => .breakStmt spanValid)
    (fun spanValid => .continueStmt spanValid)
    (fun spanValid => .error spanValid)
    (fun spanValid patternValid bodySpanValid _ bodyInduction =>
      .arm spanValid (liftPattern patternValid) bodySpanValid bodyInduction)
    (fun spanValid _ defaultSpanValid _ casesInduction defaultInduction =>
      .arms spanValid casesInduction defaultSpanValid defaultInduction)
    valid

namespace CoreStatement

/--
The depth-indexed approximation to recursive Core source-validity.  Depth only
decreases when an expression crosses into a lambda statement body; ordinary
statement nesting remains covered by `Statement.ValidFor` itself.
-/
def ValidForAt : Nat → SourceFile → Statement → Prop
  | 0, _, _ => True
  | depth + 1, file, statement =>
      Statement.ValidFor
        (Expr.ValidFor (ValidForAt depth))
        (Pattern.ValidFor (Expr.ValidFor (ValidForAt depth)))
        YulStmt.ValidFor file statement

/-- A Core statement is valid at every finite lambda/statement depth. -/
def ValidFor (file : SourceFile) (statement : Statement) : Prop :=
  ∀ depth, ValidForAt depth file statement

end CoreStatement

/-- Canonical recursive source-validity for Core expressions. -/
abbrev CoreExpr.ValidFor : SourceFile → Expr → Prop :=
  Expr.ValidFor CoreStatement.ValidFor

/-- Canonical recursive source-validity for Core patterns. -/
abbrev CorePattern.ValidFor : SourceFile → Pattern → Prop :=
  Pattern.ValidFor CoreExpr.ValidFor

namespace CoreStatement.ValidFor

/-- One well-formed statement layer closes the canonical recursive contract. -/
theorem ofStatement {file : SourceFile} {statement : Statement}
    (valid : Statement.ValidFor CoreExpr.ValidFor CorePattern.ValidFor
      YulStmt.ValidFor file statement) :
    CoreStatement.ValidFor file statement := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth =>
      exact valid.mono
        (fun expressionValid => expressionValid.mono
          (fun statementValid => statementValid depth))
        (fun patternValid => patternValid.mono fun expressionValid =>
          expressionValid.mono fun statementValid => statementValid depth)
        (fun yulValid => yulValid)

/-- A canonically valid Core statement has a source-valid outer range. -/
theorem span_valid {file : SourceFile} {statement : Statement}
    (valid : CoreStatement.ValidFor file statement) :
    statement.span.ValidFor file :=
  (valid 1).span_valid

end CoreStatement.ValidFor

end Solcore.Syntax
end
