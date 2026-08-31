import Solcore.Syntax.Module

set_option autoImplicit false

namespace Solcore.Syntax

/-- One trait path named by `#[derive(...)]`. -/
abbrev DeriveTarget := QualifiedName

/-- Canonical derive attribute attached only to an enum declaration. -/
structure DeriveAttributeValue where
  targets : NonemptyDelimitedList DeriveTarget
  deriving Repr, BEq, DecidableEq

abbrev DeriveAttribute := Located DeriveAttributeValue

/-- Provisional transparent type-alias declaration. -/
structure TypeAliasDeclValue where
  name : Identifier
  parameters : Option (DelimitedList Identifier)
  value : TypeExpr
  deriving Repr, BEq

abbrev TypeAliasDecl := Located TypeAliasDeclValue

/-- One constructor in a canonical algebraic enum declaration. -/
structure EnumConstructorValue where
  leadingComments : List Comment
  name : Identifier
  fields : Option (DelimitedList TypeExpr)
  deriving Repr, BEq

abbrev EnumConstructor := Located EnumConstructorValue

/-- Canonical algebraic enum declaration. -/
structure EnumDeclValue where
  deriveAttribute : Option DeriveAttribute
  name : Identifier
  parameters : Option GenericParameters
  bodySpan : SourceSpan
  constructors : List EnumConstructor
  deriving Repr, BEq

abbrev EnumDecl := Located EnumDeclValue

/-- Contract-only function modifiers in their canonical fixed order. -/
structure FunctionModifiers where
  publicMarker : Option SourceSpan
  payableMarker : Option SourceSpan
  deriving Repr, BEq, DecidableEq

/-- Explicit `returns (...)` clause; absence fixes the result type to unit. -/
structure ReturnClause where
  span : SourceSpan
  types : DelimitedList TypeExpr
  deriving Repr, BEq

/-- Signature shared by named functions and trait methods. -/
structure FunctionSignature where
  span : SourceSpan
  name : Identifier
  genericParameters : Option GenericParameters
  parameters : DelimitedList FunctionParameter
  modifiers : FunctionModifiers
  returnsClause : Option ReturnClause
  whereClause : Option WhereClause
  deriving Repr, BEq

/-- Ordinary named function with a parsed canonical body. -/
structure FunctionDeclValue where
  signature : FunctionSignature
  body : Block
  deriving Repr, BEq

abbrev FunctionDecl := Located FunctionDeclValue

/-- Trait method declaration terminated by `;` rather than a body. -/
structure TraitMethodValue where
  leadingComments : List Comment
  signature : FunctionSignature
  semicolon : SourceSpan
  deriving Repr, BEq

abbrev TraitMethod := Located TraitMethodValue

/-- Canonical `trait` declaration. -/
structure TraitDeclValue where
  name : Identifier
  genericParameters : GenericParameters
  whereClause : Option WhereClause
  bodySpan : SourceSpan
  methods : List TraitMethod
  deriving Repr, BEq

abbrev TraitDecl := Located TraitDeclValue

/-- Canonical `impl` declaration. -/
structure ImplDeclValue where
  defaultMarker : Option SourceSpan
  genericParameters : Option GenericParameters
  traitName : Identifier
  headArguments : NonemptyDelimitedList TypeExpr
  whereClause : Option WhereClause
  bodySpan : SourceSpan
  methods : List FunctionDecl
  deriving Repr, BEq

abbrev ImplDecl := Located ImplDeclValue

/-- One contract storage field. -/
structure ContractFieldValue where
  name : Identifier
  type : TypeExpr
  initializer : Option Expr
  deriving Repr, BEq

abbrev ContractField := Located ContractFieldValue

/-- Canonical contract constructor. -/
structure ConstructorDeclValue where
  parameters : DelimitedList FunctionParameter
  payableMarker : Option SourceSpan
  body : Block
  deriving Repr, BEq

abbrev ConstructorDecl := Located ConstructorDeclValue

/-- Canonical general fallback entry point. Its valid parameter list is empty. -/
structure FallbackDeclValue where
  parameters : DelimitedList FunctionParameter
  payableMarker : Option SourceSpan
  body : Block
  deriving Repr, BEq

abbrev FallbackDecl := Located FallbackDeclValue

/-- Declaration form accepted inside a contract body. -/
inductive ContractMemberValue where
  | field (declaration : ContractField)
  | function (declaration : FunctionDecl)
  | constructor (declaration : ConstructorDecl)
  | fallback (declaration : FallbackDecl)
  | typeAlias (declaration : TypeAliasDecl)
  | enum (declaration : EnumDecl)
  | error
  deriving Repr, BEq

/-- One contract member plus comments immediately preceding it. -/
structure ContractMember where
  span : SourceSpan
  leadingComments : List Comment
  value : ContractMemberValue
  deriving Repr, BEq

/-- Canonical contract declaration, retaining source member order. -/
structure ContractDeclValue where
  name : Identifier
  genericParameters : Option GenericParameters
  bodySpan : SourceSpan
  members : List ContractMember
  deriving Repr, BEq

abbrev ContractDecl := Located ContractDeclValue

/-- Complete top-level declaration catalog of the pinned canonical parser. -/
inductive TopItemValue where
  | importDecl (declaration : ImportDecl)
  | exportDecl (declaration : ExportDecl)
  | pragmaDecl (declaration : PragmaDecl)
  | typeAlias (declaration : TypeAliasDecl)
  | enum (declaration : EnumDecl)
  | trait (declaration : TraitDecl)
  | impl (declaration : ImplDecl)
  | contract (declaration : ContractDecl)
  | function (declaration : FunctionDecl)
  | error
  deriving Repr, BEq

/-- One top-level item plus comments immediately preceding it. -/
structure TopItem where
  span : SourceSpan
  leadingComments : List Comment
  value : TopItemValue
  deriving Repr, BEq

/-- Complete parsed source with all lexical comments retained in source order. -/
structure ParsedFile where
  source : SourceId
  span : SourceSpan
  items : List TopItem
  comments : List Comment
  deriving Repr, BEq

end Solcore.Syntax
