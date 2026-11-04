import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Grammar.Signatures
import Solcore.Syntax.Grammar.Types
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Declaration
import Solcore.Syntax.Grammar.TermLevels

/-!
Declarative grammar of declarations.

Main declarations: `TraitDeclOrdinaryParses`, `DeriveAttributeRecoveredParses`,
`TypeAliasParametersOrdinaryParses`, and the body-bearing `ContractBodyOrdinaryParses` and
`ImplBodyOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeGrammar
/-!
Parser-independent exact ordinary outcomes for malformed derive-attribute
recovery.  This file describes only the proof-visible recovery parser, not the
public transactional choice between the normal and recovered paths.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact declaration boundaries at which an unclosed derive attribute stops
without consuming the following declaration or contract closing brace. -/
inductive DeriveAttributeRecoveryDeclarationStartsAt :
    Remainder → Prop where
  | topItem {input : Remainder}
      (starts : ImportTerminatorTopItemStartsAt input) :
      DeriveAttributeRecoveryDeclarationStartsAt input
  | contractField {input : Remainder}
      (starts : ContractFieldStartsAt input) :
      DeriveAttributeRecoveryDeclarationStartsAt input
  | rightBrace {input : Remainder} (span : SourceSpan)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      DeriveAttributeRecoveryDeclarationStartsAt input

/-- Exact nonconsuming stops of the malformed derive-tail scan.  A missing
array slot inside the active window is an unclosed recovery success rather
than a rejection. -/
inductive DeriveAttributeRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      DeriveAttributeRecoveryStops input
  | declaration {input : Remainder}
      (starts : DeriveAttributeRecoveryDeclarationStartsAt input) :
      DeriveAttributeRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      DeriveAttributeRecoveryStops input

/-- Canonical empty-target AST returned by either malformed or unclosed derive
recovery.  Both the outer attribute and its empty target list use the cover
from the original hash through the last retained span. -/
def recoveredDeriveAttributeValue
    (hash last : SourceSpan) : Syntax.DeriveAttribute :=
  let span := SourceSpan.cover hash last
  {
    span
    value := { targets := { span, elements := [] } }
  }

/-- Exact priority-ordered scan after recovery has consumed `#[`.  A current
`]` is consumed before any stop is considered.  Otherwise a stop returns an
unclosed value without consumption, and any remaining current token advances
the scan by one. -/
inductive DeriveAttributeRecoveryTailParses (hash : SourceSpan) :
    SourceSpan → Remainder → Syntax.DeriveAttribute → Remainder → Prop where
  | malformed {last : SourceSpan} {input output : Remainder}
      (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBracket) input
        closingSpan output) :
      DeriveAttributeRecoveryTailParses hash last input
        (recoveredDeriveAttributeValue hash closingSpan) output
  | unclosed {last : SourceSpan} {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBracket))
      (stops : DeriveAttributeRecoveryStops input) :
      DeriveAttributeRecoveryTailParses hash last input
        (recoveredDeriveAttributeValue hash last) input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {value : Syntax.DeriveAttribute}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBracket))
      (continues : ¬ DeriveAttributeRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : DeriveAttributeRecoveryTailParses hash token.span
        { input with cursor := input.cursor + 1 } value output) :
      DeriveAttributeRecoveryTailParses hash last input value output

/-- Exact successful recovery path: consume hash and opening bracket, then run
the malformed tail from the opening bracket's span. -/
inductive DeriveAttributeRecoveredParses :
    Remainder → Syntax.DeriveAttribute → Remainder → Prop where
  | recovered {input afterHash afterOpening output : Remainder}
      {value : Syntax.DeriveAttribute}
      (hashSpan openingSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (tail : DeriveAttributeRecoveryTailParses hashSpan openingSpan
        afterOpening value output) :
      DeriveAttributeRecoveredParses input value output

/-- Recovery can reject only before its tail begins: at the initial hash or at
the opening bracket after a consumed hash. -/
inductive DeriveAttributeRecoveredRejects : Remainder → Remainder → Prop where
  | hashMissing {input : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash)) :
      DeriveAttributeRecoveredRejects input input
  | openingMissing {input afterHash : Remainder} (hashSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingAbsent : TokenKindAbsentAt afterHash.tokens afterHash.endIndex
        afterHash.cursor (.symbol .leftBracket)) :
      DeriveAttributeRecoveredRejects input afterHash

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitMethodOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for one
signature-only trait method.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordinary trait method is a broad ordinary function signature followed
by its exact terminating semicolon. -/
inductive TraitMethodOrdinaryParses :
    Remainder → Syntax.TraitMethod → Remainder → Prop where
  | parsed {input afterSignature output : Remainder}
      {signature : Syntax.FunctionSignature} (semicolonSpan : SourceSpan)
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterSignature semicolonSpan output) :
      TraitMethodOrdinaryParses input {
        span := SourceSpan.cover signature.span semicolonSpan
        value := {
          leadingComments := []
          signature
          semicolon := semicolonSpan
        }
      } output

/-- Exact first rejecting stage of an ordinary trait-method attempt. -/
inductive TraitMethodRejects : Remainder → Remainder → Prop where
  | signatureRejected {input rejected : Remainder}
      (signatureRejected : FunctionSignatureRejects input rejected) :
      TraitMethodRejects input rejected
  | semicolonMissing {input afterSignature : Remainder}
      {signature : Syntax.FunctionSignature}
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (semicolonAbsent : TokenKindAbsentAt afterSignature.tokens
        afterSignature.endIndex afterSignature.cursor (.symbol .semicolon)) :
      TraitMethodRejects input afterSignature

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitBodyOutcomeGrammar
/-!
Parser-independent ordinary success and exact rejection for the prioritized
trait-method body loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive `function` lookahead selecting the method branch. -/
def TraitMethodStartAt (input : Remainder) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span, value := .keyword .functionKw }

/-- Forward ordinary methods ending at the exact closing brace.  The closing
branch has priority, and the method branch records its positive guard and
strict cursor progress independently of the executable fuel bound. -/
inductive TraitMethodTailOrdinaryParses :
    Remainder → List Syntax.TraitMethod → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      TraitMethodTailOrdinaryParses input [] closingSpan output
  | next {input afterMethod output : Remainder}
      {method : Syntax.TraitMethod} {methods : List Syntax.TraitMethod}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : TraitMethodStartAt input)
      (methodParsed : TraitMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tail : TraitMethodTailOrdinaryParses afterMethod methods closingSpan
        output) :
      TraitMethodTailOrdinaryParses input (method :: methods) closingSpan
        output

/-- Single-output adapter retaining the closing span and forward methods. -/
def TraitMethodTailOrdinaryOutcomeParses (input : Remainder)
    (tail : SourceSpan × List Syntax.TraitMethod)
    (output : Remainder) : Prop :=
  TraitMethodTailOrdinaryParses input tail.2 tail.1 output

/-- Exact ordinary rejection of the prioritized trait-method loop. -/
inductive TraitMethodTailRejects : Remainder → Remainder → Prop where
  | unexpected {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw)) :
      TraitMethodTailRejects input input
  | methodRejected {input rejected : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : TraitMethodStartAt input)
      (methodRejected : TraitMethodRejects input rejected) :
      TraitMethodTailRejects input rejected
  | laterRejected {input afterMethod rejected : Remainder}
      {method : Syntax.TraitMethod}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : TraitMethodStartAt input)
      (methodParsed : TraitMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tailRejected : TraitMethodTailRejects afterMethod rejected) :
      TraitMethodTailRejects input rejected

/-- Exact braces, retained body span, and source-order ordinary trait methods. -/
inductive TraitBodyOrdinaryParses :
    Remainder → SourceSpan → List Syntax.TraitMethod →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {methods : List Syntax.TraitMethod} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (methodsParsed : TraitMethodTailOrdinaryParses afterOpening methods
        closingSpan output) :
      TraitBodyOrdinaryParses input (SourceSpan.cover openingSpan closingSpan)
        methods output

/-- Single-output adapter retaining the body span and forward methods. -/
def TraitBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.TraitMethod)
    (output : Remainder) : Prop :=
  TraitBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of a complete braced trait body. -/
inductive TraitBodyRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      TraitBodyRejects input input
  | tailRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (tailRejected : TraitMethodTailRejects afterOpening rejected) :
      TraitBodyRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTraitDeclarationOutcomeGrammar
/-! Parser-independent ordinary outcomes for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad trait declaration in executable stage order. -/
inductive TraitDeclOrdinaryParses :
    Remainder → Syntax.TraitDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterName afterGenerics afterWhere output : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Syntax.GenericParameters}
      {whereClause : Option Syntax.WhereClause} {bodySpan : SourceSpan}
      {methods : List Syntax.TraitMethod} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : GenericParametersParses afterName genericParameters
        afterGenerics)
      (whereParsed : OptionalWhereClauseParses afterGenerics whereClause
        afterWhere)
      (bodyParsed : TraitBodyOrdinaryParses afterWhere bodySpan methods
        output) :
      TraitDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := {
          name
          genericParameters
          whereClause
          bodySpan
          methods
        }
      } output

/-- Exact first rejecting stage of one broad trait-declaration attempt. -/
inductive TraitDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.trait.spelling)) :
      TraitDeclRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      TraitDeclRejects input rejected
  | genericsRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsRejected : GenericParametersRejects afterName rejected) :
      TraitDeclRejects input rejected
  | whereRejected
      {input afterMarker afterName afterGenerics rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Syntax.GenericParameters} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : GenericParametersParses afterName genericParameters
        afterGenerics)
      (whereRejected : OptionalWhereClauseRejects afterGenerics rejected) :
      TraitDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterName afterGenerics afterWhere rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Syntax.GenericParameters}
      {whereClause : Option Syntax.WhereClause} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : GenericParametersParses afterName genericParameters
        afterGenerics)
      (whereParsed : OptionalWhereClauseParses afterGenerics whereClause
        afterWhere)
      (bodyRejected : TraitBodyRejects afterWhere rejected) :
      TraitDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractFieldOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for one
contract storage field, parameterized by the initializer expression outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional field initializers reuse the exact prioritized strict
success grammar with an abstract expression success relation. -/
abbrev OptionalContractFieldInitializerOrdinaryParses :=
  OptionalContractFieldInitializerParses

/-- A present field initializer rejects only after consuming its exact `=`
token and rejecting the initializer expression. -/
inductive OptionalContractFieldInitializerRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | expressionRejected {input afterEqual rejected : Remainder}
      (equalSpan : SourceSpan)
      (equalParsed : ExactTokenParses (.symbol .equal) input equalSpan
        afterEqual)
      (expressionRejected : expressionRejects afterEqual rejected) :
      OptionalContractFieldInitializerRejects expressionRejects input rejected

/-- Ordinary storage-field success is the existing exact parametric grammar;
public type ordinary success is definitionally the same fixed Core type
grammar used there. -/
abbrev ContractFieldOrdinaryParses := ContractFieldParses

/-- Exact first rejecting stage of one storage-field attempt. -/
inductive ContractFieldRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | nameRejected {input rejected : Remainder}
      (nameRejected : IdentifierRejects input rejected) :
      ContractFieldRejects expressionOrdinary expressionRejects input rejected
  | colonMissing {input afterName : Remainder} {name : Syntax.Identifier}
      (nameParsed : IdentifierParses input name afterName)
      (colonAbsent : TokenKindAbsentAt afterName.tokens afterName.endIndex
        afterName.cursor (.symbol .colon)) :
      ContractFieldRejects expressionOrdinary expressionRejects input afterName
  | typeRejected {input afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (colonSpan : SourceSpan)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : TypeExprRejects afterColon rejected) :
      ContractFieldRejects expressionOrdinary expressionRejects input rejected
  | initializerRejected
      {input afterName afterColon afterType rejected : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : TypeExprOrdinaryParses afterColon type afterType)
      (initializerRejected : OptionalContractFieldInitializerRejects
        expressionRejects afterType rejected) :
      ContractFieldRejects expressionOrdinary expressionRejects input rejected
  | semicolonMissing
      {input afterName afterColon afterType afterInitializer : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      {initializer : Option Syntax.Expr} (colonSpan : SourceSpan)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : TypeExprOrdinaryParses afterColon type afterType)
      (initializerParsed : OptionalContractFieldInitializerOrdinaryParses
        expressionOrdinary afterType initializer afterInitializer)
      (semicolonAbsent : TokenKindAbsentAt afterInitializer.tokens
        afterInitializer.endIndex afterInitializer.cursor (.symbol .semicolon)) :
      ContractFieldRejects expressionOrdinary expressionRejects input
        afterInitializer

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumConstructorOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for enum
constructors and their optional tuple payloads.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional constructor fields reuse the exact prioritized grammar
with public Core type success. -/
abbrev OptionalEnumConstructorFieldsOrdinaryParses :=
  OptionalEnumConstructorFieldsParses

/-- A positive `(` lookahead commits optional constructor fields to the
allow-empty, no-trailing delimited attempt. -/
inductive OptionalEnumConstructorFieldsRejects :
    Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (openingPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span, value := .symbol .leftParen })
      (fieldsRejected : DelimitedListRejects .leftParen .rightParen true false
        TypeExprOrdinaryParses TypeExprRejects input rejected) :
      OptionalEnumConstructorFieldsRejects input rejected

/-- Ordinary enum-constructor success is the existing exact retained grammar. -/
abbrev EnumConstructorOrdinaryParses := EnumConstructorParses

/-- Exact first rejecting stage of one enum-constructor attempt. -/
inductive EnumConstructorRejects : Remainder → Remainder → Prop where
  | nameRejected {input rejected : Remainder}
      (nameRejected : IdentifierRejects input rejected) :
      EnumConstructorRejects input rejected
  | fieldsRejected {input afterName rejected : Remainder}
      {name : Syntax.Identifier}
      (nameParsed : IdentifierParses input name afterName)
      (fieldsRejected : OptionalEnumConstructorFieldsRejects afterName
        rejected) :
      EnumConstructorRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumBodyOutcomeGrammar
/-! Parser-independent ordinary outcomes for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary enum-body success is the existing exact possibly-empty,
trailing-comma grammar. -/
abbrev EnumBodyOrdinaryParses := EnumBodyParses

/-- Single-output adapter retaining the body span and constructor list. -/
def EnumBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.EnumConstructor)
    (output : Remainder) : Prop :=
  EnumBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of the allow-empty, allow-trailing enum body. -/
abbrev EnumBodyRejects :=
  DelimitedListRejects .leftBrace .rightBrace true true
    EnumConstructorOrdinaryParses EnumConstructorRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeEnumDeclarationOutcomeGrammar
/-! Parser-independent ordinary outcomes for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary enum declarations reuse the exact grammar at one supplied derive
attribute. -/
abbrev EnumDeclOrdinaryParses
    (deriveAttribute : Option Syntax.DeriveAttribute) :=
  EnumDeclParses deriveAttribute

/-- Exact first rejecting stage of one enum-declaration attempt. -/
inductive EnumDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling)) :
      EnumDeclRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.enum.spelling)
        input markerSpan afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      EnumDeclRejects input rejected
  | parametersRejected
      {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.enum.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (parametersRejected : OptionalGenericParametersRejects afterName
        rejected) :
      EnumDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterName afterParameters rejected : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option Syntax.GenericParameters} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.enum.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (parametersParsed : OptionalGenericParametersParses afterName parameters
        afterParameters)
      (bodyRejected : EnumBodyRejects afterParameters rejected) :
      EnumDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeAliasOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for type
alias parameters, recovery-aware alias values, and complete declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-! Optional parenthesized alias parameters. -/

/-- Exact allow-empty, allow-trailing type-alias parameter list. -/
abbrev TypeAliasParametersOrdinaryParses :=
  TrailingDelimitedListParses .leftParen .rightParen IdentifierParses

/-- Exact rejection of an allow-empty, allow-trailing alias parameter list. -/
abbrev TypeAliasParametersRejects :=
  DelimitedListRejects .leftParen .rightParen true true IdentifierParses
    IdentifierRejects

/-- Ordinary optional alias-parameter success is the existing exact grammar. -/
abbrev OptionalTypeAliasParametersOrdinaryParses :=
  OptionalTypeAliasParametersParses

/-- A positive `(` lookahead commits optional alias parameters to the complete
delimited-list attempt from the original remainder. -/
inductive OptionalTypeAliasParametersRejects : Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (openingPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span, value := .symbol .leftParen })
      (parametersRejected : TypeAliasParametersRejects input rejected) :
      OptionalTypeAliasParametersRejects input rejected

/-! Recovery-aware type-alias values. -/

/-- Exact non-consuming boundaries checked before alias-value recovery. -/
inductive TypeAliasValueBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TypeAliasValueBoundaryStops input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      TypeAliasValueBoundaryStops input

/-- Exact stops of the scan after recovery consumed its mandatory first token.
A missing carrier slot here finishes recovery rather than rejecting it. -/
inductive TypeAliasValueRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      TypeAliasValueRecoveryStops input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      TypeAliasValueRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TypeAliasValueRecoveryStops input

/-- Exact scan after alias-value recovery consumed its mandatory first token. -/
inductive TypeAliasValueRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.TypeExpr → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : TypeAliasValueRecoveryStops input) :
      TypeAliasValueRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {value : Syntax.TypeExpr}
      (continues : ¬ TypeAliasValueRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : TypeAliasValueRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } value output) :
      TypeAliasValueRecoveryScanParses first last input value output

/-- Successful alias-value recovery, including its mandatory first token. -/
inductive TypeAliasValueRecoveryParses :
    Remainder → Syntax.TypeExpr → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {value : Syntax.TypeExpr}
      (continues : ¬ TypeAliasValueBoundaryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : TypeAliasValueRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } value output) :
      TypeAliasValueRecoveryParses input value output

/-- Exact non-consuming rejection when recovery cannot consume its first token. -/
inductive TypeAliasValueRecoveryRejects : Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (stops : TypeAliasValueBoundaryStops input) :
      TypeAliasValueRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      TypeAliasValueRecoveryRejects input input

/-- A rejected Core type retains its failed cursor while preserving the token
carrier and active window needed for the alias-value rewind. -/
def TypeAliasValueCoreRejectsWithPreservedWindow (input : Remainder) : Prop :=
  ∃ failed, TypeExprRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Direct Core type success or exact recovery from the original cursor. -/
inductive TypeAliasValueOrdinaryParses :
    Remainder → Syntax.TypeExpr → Remainder → Prop where
  | core {input output : Remainder} {value : Syntax.TypeExpr}
      (parsed : TypeExprOrdinaryParses input value output) :
      TypeAliasValueOrdinaryParses input value output
  | recovered {input output : Remainder} {value : Syntax.TypeExpr}
      (coreRejected : TypeAliasValueCoreRejectsWithPreservedWindow input)
      (recovered : TypeAliasValueRecoveryParses input value output) :
      TypeAliasValueOrdinaryParses input value output

/-- Exact public alias-value rejection at the rewound boundary or in recovery. -/
inductive TypeAliasValueRejects : Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : TypeAliasValueCoreRejectsWithPreservedWindow input)
      (stops : TypeAliasValueBoundaryStops input) :
      TypeAliasValueRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : TypeAliasValueCoreRejectsWithPreservedWindow input)
      (continues : ¬ TypeAliasValueBoundaryStops input)
      (recoveryRejected : TypeAliasValueRecoveryRejects input rejected) :
      TypeAliasValueRejects input rejected

/-! Complete broad type-alias outcomes. -/

/-- Exact broad type-alias success in executable stage order. -/
inductive TypeAliasDeclOrdinaryParses :
    Remainder → Syntax.TypeAliasDecl → Remainder → Prop where
  | parsed
      {input afterKeyword afterName afterParameters afterEqual afterValue
        output : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      {value : Syntax.TypeExpr}
      (keywordSpan equalSpan semicolonSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalParsed : ExactTokenParses (.symbol .equal)
        afterParameters equalSpan afterEqual)
      (valueParsed : TypeAliasValueOrdinaryParses afterEqual value afterValue)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterValue semicolonSpan output) :
      TypeAliasDeclOrdinaryParses input {
        span := SourceSpan.cover keywordSpan semicolonSpan
        value := { name, parameters, value }
      } output

/-- Exact first rejecting stage of one broad type-alias attempt. -/
inductive TypeAliasDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw)) :
      TypeAliasDeclRejects input input
  | nameRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameRejected : IdentifierRejects afterKeyword rejected) :
      TypeAliasDeclRejects input rejected
  | parametersRejected
      {input afterKeyword afterName rejected : Remainder}
      {name : Syntax.Identifier} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersRejected : OptionalTypeAliasParametersRejects afterName
        rejected) :
      TypeAliasDeclRejects input rejected
  | equalMissing
      {input afterKeyword afterName afterParameters : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalAbsent : TokenKindAbsentAt afterParameters.tokens
        afterParameters.endIndex afterParameters.cursor (.symbol .equal)) :
      TypeAliasDeclRejects input afterParameters
  | valueRejected
      {input afterKeyword afterName afterParameters afterEqual rejected : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      (keywordSpan equalSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalParsed : ExactTokenParses (.symbol .equal)
        afterParameters equalSpan afterEqual)
      (valueRejected : TypeAliasValueRejects afterEqual rejected) :
      TypeAliasDeclRejects input rejected
  | semicolonMissing
      {input afterKeyword afterName afterParameters afterEqual afterValue : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option (DelimitedList Syntax.Identifier)}
      {value : Syntax.TypeExpr} (keywordSpan equalSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .typeKw)
        input keywordSpan afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (parametersParsed : OptionalTypeAliasParametersOrdinaryParses
        afterName parameters afterParameters)
      (equalParsed : ExactTokenParses (.symbol .equal)
        afterParameters equalSpan afterEqual)
      (valueParsed : TypeAliasValueOrdinaryParses afterEqual value afterValue)
      (semicolonAbsent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex
        afterValue.cursor (.symbol .semicolon)) :
      TypeAliasDeclRejects input afterValue

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeGrammar
/-! Broad ordinary outcomes for required implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A nonempty angle-delimited list of broad ordinary type expressions,
adapted exactly to the AST's nonempty container. -/
def ImplHeadArgumentsOrdinaryParses
    (input : Remainder)
    (arguments : NonemptyDelimitedList Syntax.TypeExpr)
    (output : Remainder) : Prop :=
  NonemptyTrailingDelimitedListParses .less .greater
    TypeExprOrdinaryParses input {
      span := arguments.span
      elements := arguments.elements.toList
    } output

/-- Exact rejection of the committed nonempty, trailing-comma angle list. -/
abbrev ImplHeadArgumentsRejects :=
  DelimitedListRejects .less .greater false true TypeExprOrdinaryParses
    TypeExprRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveTargetOutcomeGrammar
/-!
Parser-independent exact rejection traces for dotted derive targets.

The established `DeriveComponentParses`, `DeriveTargetTailParses`, and
`DeriveTargetParses` relations already describe every ordinary success,
including diagnosed reserved-keyword components.  The relations below add
the complementary rejection path without changing those successes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- No hard keyword admitted as a diagnosed derive component occurs at the
current cursor. -/
def DeriveReservedComponentAbsentAt (input : Remainder) : Prop :=
  ∀ keyword, ReservedDeriveTargetKeyword keyword →
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword keyword)

/-- Exact nonconsuming rejection of one derive component after both the
reserved-keyword recovery branch and the identifier branch are unavailable. -/
inductive DeriveComponentRejects : Remainder → Remainder → Prop where
  | unavailable {input : Remainder}
      (reservedAbsent : DeriveReservedComponentAbsentAt input)
      (identifierRejected : IdentifierRejects input input) :
      DeriveComponentRejects input input

/-- Exact rejection while consuming the dotted tail of one derive target.
The dot advances once before a component rejection; a successful component
delegates only to the later tail. -/
inductive DeriveTargetTailRejects : Remainder → Remainder → Prop where
  | componentRejected {input afterDot rejected : Remainder}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (componentRejected : DeriveComponentRejects afterDot rejected) :
      DeriveTargetTailRejects input rejected
  | laterRejected {input afterDot afterComponent rejected : Remainder}
      {component : Syntax.Identifier} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (componentParsed : DeriveComponentParses afterDot component
        afterComponent)
      (laterRejected : DeriveTargetTailRejects afterComponent rejected) :
      DeriveTargetTailRejects input rejected

/-- Exact first or later component rejection of a complete derive target. -/
inductive DeriveTargetRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (componentRejected : DeriveComponentRejects input rejected) :
      DeriveTargetRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier}
      (firstParsed : DeriveComponentParses input first afterFirst)
      (tailRejected : DeriveTargetTailRejects afterFirst rejected) :
      DeriveTargetRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeGrammar
/-!
Parser-independent exact rejection stages for the normal derive-attribute
path.  The successful path remains the established `DeriveAttributeParses`
relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact first rejecting stage of the proof-visible normal derive-attribute
parser.  Diagnostic emission after the closing bracket and the final pure
construction cannot reject. -/
inductive DeriveAttributeValidRejects : Remainder → Remainder → Prop where
  | hashMissing {input : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash)) :
      DeriveAttributeValidRejects input input
  | openingMissing {input afterHash : Remainder} (hashSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingAbsent : TokenKindAbsentAt afterHash.tokens afterHash.endIndex
        afterHash.cursor (.symbol .leftBracket)) :
      DeriveAttributeValidRejects input afterHash
  | markerMissing {input afterHash afterOpening : Remainder}
      (hashSpan openingSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (markerAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor
        (.identifier ContextualKeyword.derive.spelling)) :
      DeriveAttributeValidRejects input afterOpening
  | targetsRejected
      {input afterHash afterOpening afterMarker rejected : Remainder}
      (hashSpan openingSpan markerSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.derive.spelling) afterOpening
        markerSpan afterMarker)
      (targetsRejected : DelimitedListRejects .leftParen .rightParen true false
        DeriveTargetParses DeriveTargetRejects afterMarker rejected) :
      DeriveAttributeValidRejects input rejected
  | closingMissing
      {input afterHash afterOpening afterMarker afterTargets : Remainder}
      {targets : Syntax.DelimitedList Syntax.DeriveTarget}
      (hashSpan openingSpan markerSpan : SourceSpan)
      (hashParsed : ExactTokenParses (.symbol .hash) input hashSpan afterHash)
      (openingParsed : ExactTokenParses (.symbol .leftBracket) afterHash
        openingSpan afterOpening)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.derive.spelling) afterOpening
        markerSpan afterMarker)
      (targetsParsed : NoTrailingDelimitedListParses .leftParen .rightParen
        DeriveTargetParses afterMarker targets afterTargets)
      (closingAbsent : TokenKindAbsentAt afterTargets.tokens
        afterTargets.endIndex afterTargets.cursor (.symbol .rightBracket)) :
      DeriveAttributeValidRejects input afterTargets

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDeriveAttributeOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for the public derive-attribute
parser's prioritized transactional choice.

The recovered path always starts again at the original input.  The rejected
remainder from the normal path is retained only as evidence that fallback was
selected.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary public success from the preferred normal path, or from recovery
selected by an exact normal-path rejection and retried at the original input. -/
inductive DeriveAttributeOrdinaryParses :
    Remainder → Syntax.DeriveAttribute → Remainder → Prop where
  | normal {input output : Remainder} {value : Syntax.DeriveAttribute}
      (parsed : DeriveAttributeParses input value output) :
      DeriveAttributeOrdinaryParses input value output
  | recovered {input validRejected output : Remainder}
      {value : Syntax.DeriveAttribute}
      (validRejection : DeriveAttributeValidRejects input validRejected)
      (parsed : DeriveAttributeRecoveredParses input value output) :
      DeriveAttributeOrdinaryParses input value output

/-- Exact public rejection when the normal path rejects and recovery, retried
at the original input, also rejects.  The public endpoint is recovery's
rejected remainder; the normal rejected remainder remains explicit evidence. -/
inductive DeriveAttributeRejects : Remainder → Remainder → Prop where
  | both {input validRejected recoveredRejected : Remainder}
      (validRejection : DeriveAttributeValidRejects input validRejected)
      (recoveredRejection : DeriveAttributeRecoveredRejects input
        recoveredRejected) :
      DeriveAttributeRejects input recoveredRejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplDefaultMarkerOutcomeGrammar
/-!
Parser-independent ordinary success and impossible rejection for the optional
leading `default` implementation marker.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional-default success is the existing exact prioritized
grammar. -/
abbrev OptionalImplDefaultMarkerOrdinaryParses :=
  OptionalImplDefaultMarkerParses

/-- The guarded optional-default parser has no executable reject branch. -/
def OptionalImplDefaultMarkerRejects (_input _rejected : Remainder) : Prop :=
  False

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractDeriveAttachmentGrammar
/-!
Parser-independent AST transformation performed when a derive attribute is
attached to one contract member.  Parser diagnostics and state are
intentionally outside this pure relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact pure result of attaching a derive attribute to a contract member.

Only enums retain the attribute.  Every other member keeps its variant and
payload while extending its outer and nested declaration spans. -/
inductive ContractDeriveAttaches :
    Syntax.DeriveAttribute → Syntax.ContractMember →
      Syntax.ContractMember → Prop where
  | field {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ContractField} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .field declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .field {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | function {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.FunctionDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .function declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .function {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | constructor {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.ConstructorDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .constructor declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .constructor {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | fallback {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.FallbackDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .fallback declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .fallback {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | typeAlias {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.TypeAliasDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .typeAlias declaration
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .typeAlias {
          declaration with
          span := SourceSpan.cover derive.span memberSpan
        }
      }
  | enum {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment}
      {declaration : Syntax.EnumDecl} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .enum declaration
      } {
        span := SourceSpan.cover derive.span declaration.span
        leadingComments
        value := .enum {
          declaration with
          span := SourceSpan.cover derive.span declaration.span
          value := {
            declaration.value with
            deriveAttribute := some derive
          }
        }
      }
  | error {derive : Syntax.DeriveAttribute} {memberSpan : SourceSpan}
      {leadingComments : List Syntax.Comment} :
      ContractDeriveAttaches derive {
        span := memberSpan
        leadingComments
        value := .error
      } {
        span := SourceSpan.cover derive.span memberSpan
        leadingComments
        value := .error
      }

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for
complete named-function declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary function declaration, including recovery-aware signature
parameters and balanced isolated-block recovery. -/
inductive FunctionDeclOrdinaryParses :
    Remainder → Syntax.FunctionDecl → Remainder → Prop where
  | parsed {input afterSignature output : Remainder}
      {signature : Syntax.FunctionSignature} {body : Syntax.Block}
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (bodyParsed : IsolatedCoreBlockPublicOrdinaryParses .allow
        afterSignature body output) :
      FunctionDeclOrdinaryParses input {
        span := SourceSpan.cover signature.span body.span
        value := { signature, body }
      } output

/-- Exact first rejecting stage of an ordinary function-declaration attempt.
Balanced child-block rejection is represented by ordinary recovered success,
so only uncaptured body rejection escapes the declaration parser. -/
inductive FunctionDeclRejects : Remainder → Remainder → Prop where
  | signatureRejected {input rejected : Remainder}
      (signatureRejected : FunctionSignatureRejects input rejected) :
      FunctionDeclRejects input rejected
  | bodyRejected {input afterSignature rejected : Remainder}
      {signature : Syntax.FunctionSignature}
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (bodyRejected : IsolatedCoreBlockPublicRejects .allow afterSignature
        rejected) :
      FunctionDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplMethodOutcomeGrammar
/-!
Parser-independent ordinary success and exact rejection for one implementation
method wrapper.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordinary implementation method is exactly a module-position function
declaration wrapped with empty parser-time leading comments. -/
inductive ImplMethodOrdinaryParses :
    Remainder → Syntax.ImplMethod → Remainder → Prop where
  | parsed {input output : Remainder}
      {declaration : Syntax.FunctionDecl}
      (declarationParsed : FunctionDeclOrdinaryParses input declaration
        output) :
      ImplMethodOrdinaryParses input {
        span := declaration.span
        value := { leadingComments := [], declaration }
      } output

/-- Implementation-method rejection is exactly its nested function-declaration
rejection; the pure wrapper adds no rejecting stage. -/
inductive ImplMethodRejects : Remainder → Remainder → Prop where
  | declarationRejected {input rejected : Remainder}
      (declarationRejected : FunctionDeclRejects input rejected) :
      ImplMethodRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplBodyOutcomeGrammar
/-!
Parser-independent ordinary success and exact rejection for the prioritized
implementation-method body loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive `function` lookahead selecting the method branch. -/
def ImplMethodStartAt (input : Remainder) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span, value := .keyword .functionKw }

/-- Forward ordinary methods ending at the exact closing brace.  The closing
branch has priority, and the method branch records its positive guard and
strict cursor progress independently of the executable fuel bound. -/
inductive ImplMethodTailOrdinaryParses :
    Remainder → List Syntax.ImplMethod → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      ImplMethodTailOrdinaryParses input [] closingSpan output
  | next {input afterMethod output : Remainder}
      {method : Syntax.ImplMethod} {methods : List Syntax.ImplMethod}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : ImplMethodStartAt input)
      (methodParsed : ImplMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tail : ImplMethodTailOrdinaryParses afterMethod methods closingSpan
        output) :
      ImplMethodTailOrdinaryParses input (method :: methods) closingSpan
        output

/-- Single-output adapter retaining the closing span and forward methods. -/
def ImplMethodTailOrdinaryOutcomeParses (input : Remainder)
    (tail : SourceSpan × List Syntax.ImplMethod)
    (output : Remainder) : Prop :=
  ImplMethodTailOrdinaryParses input tail.2 tail.1 output

/-- Exact ordinary rejection of the prioritized implementation-method loop. -/
inductive ImplMethodTailRejects : Remainder → Remainder → Prop where
  | unexpected {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw)) :
      ImplMethodTailRejects input input
  | methodRejected {input rejected : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : ImplMethodStartAt input)
      (methodRejected : ImplMethodRejects input rejected) :
      ImplMethodTailRejects input rejected
  | laterRejected {input afterMethod rejected : Remainder}
      {method : Syntax.ImplMethod}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (functionPresent : ImplMethodStartAt input)
      (methodParsed : ImplMethodOrdinaryParses input method afterMethod)
      (progress : input.cursor < afterMethod.cursor)
      (tailRejected : ImplMethodTailRejects afterMethod rejected) :
      ImplMethodTailRejects input rejected

/-- Exact braces, retained body span, and source-order ordinary methods. -/
inductive ImplBodyOrdinaryParses :
    Remainder → SourceSpan → List Syntax.ImplMethod →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {methods : List Syntax.ImplMethod} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (methodsParsed : ImplMethodTailOrdinaryParses afterOpening methods
        closingSpan output) :
      ImplBodyOrdinaryParses input (SourceSpan.cover openingSpan closingSpan)
        methods output

/-- Single-output adapter retaining the body span and forward methods. -/
def ImplBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.ImplMethod)
    (output : Remainder) : Prop :=
  ImplBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of a complete braced implementation body. -/
inductive ImplBodyRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      ImplBodyRejects input input
  | tailRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (tailRejected : ImplMethodTailRejects afterOpening rejected) :
      ImplBodyRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeImplDeclarationOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad implementation declaration in executable stage order. -/
inductive ImplDeclOrdinaryParses :
    Remainder → Syntax.ImplDecl → Remainder → Prop where
  | parsed
      {input afterDefault afterMarker afterGenerics afterName afterArguments
        afterWhere output : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      {headArguments : NonemptyDelimitedList Syntax.TypeExpr}
      {whereClause : Option Syntax.WhereClause} {bodySpan : SourceSpan}
      {methods : List Syntax.ImplMethod}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsParsed : ImplHeadArgumentsOrdinaryParses afterName
        headArguments afterArguments)
      (whereParsed : OptionalWhereClauseParses afterArguments whereClause
        afterWhere)
      (bodyParsed : ImplBodyOrdinaryParses afterWhere bodySpan methods
        output) :
      ImplDeclOrdinaryParses input {
        span := SourceSpan.cover (defaultMarker.getD markerSpan) bodySpan
        value := {
          defaultMarker
          genericParameters
          traitName
          headArguments
          whereClause
          bodySpan
          methods
        }
      } output

/-- Exact first rejecting stage after the infallible optional-default prefix. -/
inductive ImplDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input afterDefault : Remainder}
      {defaultMarker : Option SourceSpan}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerAbsent : TokenKindAbsentAt afterDefault.tokens
        afterDefault.endIndex afterDefault.cursor
        (.identifier ContextualKeyword.impl.spelling)) :
      ImplDeclRejects input afterDefault
  | genericsRejected {input afterDefault afterMarker rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsRejected : OptionalGenericParametersRejects afterMarker
        rejected) :
      ImplDeclRejects input rejected
  | nameRejected
      {input afterDefault afterMarker afterGenerics rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameRejected : IdentifierRejects afterGenerics rejected) :
      ImplDeclRejects input rejected
  | argumentsRejected
      {input afterDefault afterMarker afterGenerics afterName rejected :
        Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsRejected : ImplHeadArgumentsRejects afterName rejected) :
      ImplDeclRejects input rejected
  | whereRejected
      {input afterDefault afterMarker afterGenerics afterName afterArguments
        rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      {headArguments : NonemptyDelimitedList Syntax.TypeExpr}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsParsed : ImplHeadArgumentsOrdinaryParses afterName
        headArguments afterArguments)
      (whereRejected : OptionalWhereClauseRejects afterArguments rejected) :
      ImplDeclRejects input rejected
  | bodyRejected
      {input afterDefault afterMarker afterGenerics afterName afterArguments
        afterWhere rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      {headArguments : NonemptyDelimitedList Syntax.TypeExpr}
      {whereClause : Option Syntax.WhereClause}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsParsed : ImplHeadArgumentsOrdinaryParses afterName
        headArguments afterArguments)
      (whereParsed : OptionalWhereClauseParses afterArguments whereClause
        afterWhere)
      (bodyRejected : ImplBodyRejects afterWhere rejected) :
      ImplDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for
canonical contract constructors.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact fixed-order ordinary entry modifiers.  The optional explicit
`public` marker remains in the derivation even though the executable AST keeps
only the optional `payable` marker. -/
inductive ContractEntryModifiersOrdinaryParses :
    Remainder → Option SourceSpan → Remainder → Prop where
  | parsed {input afterPublic output : Remainder}
      {publicMarker payableMarker : Option SourceSpan}
      (publicParsed : OptionalFunctionModifierParses .publicKw input
        publicMarker afterPublic)
      (payableParsed : OptionalFunctionModifierParses .payableKw afterPublic
        payableMarker output) :
      ContractEntryModifiersOrdinaryParses input payableMarker output

/-- Exact ordinary constructor success, including diagnosed parameters,
discarded explicit `public`, and balanced required-body recovery. -/
inductive ConstructorDeclOrdinaryParses :
    Remainder → Syntax.ConstructorDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterParameters afterModifiers output : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .constructorKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterParameters
        payableMarker afterModifiers)
      (bodyParsed : IsolatedCoreBlockPublicOrdinaryParses .require
        afterModifiers body output) :
      ConstructorDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan body.span
        value := { parameters, payableMarker, body }
      } output

/-- Exact first rejecting stage of an ordinary constructor attempt.  Entry
modifiers cannot reject, so rejection occurs at the marker, parameters, or
uncaptured required body. -/
inductive ConstructorDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw)) :
      ConstructorDeclRejects input input
  | parametersRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .constructorKw)
        input markerSpan afterMarker)
      (parametersRejected : FunctionParametersRejects afterMarker rejected) :
      ConstructorDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterParameters afterModifiers rejected : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .constructorKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterParameters
        payableMarker afterModifiers)
      (bodyRejected : IsolatedCoreBlockPublicRejects .require afterModifiers
        rejected) :
      ConstructorDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeGrammar
/-!
Parser-independent ordinary success and exact sequential rejection for
canonical contract fallback declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fallback parameter validation is a pure stage.  Empty parameters pass
silently, while retained nonempty parameters take the diagnosed success path;
neither branch consumes a token. -/
inductive FallbackParameterValidationOrdinaryParses
    (parameters : DelimitedList Syntax.FunctionParameter) :
    Remainder → Remainder → Prop where
  | empty {input : Remainder}
      (parameterless : parameters.elements = []) :
      FallbackParameterValidationOrdinaryParses parameters input input
  | diagnosed {input : Remainder}
      (nonempty : parameters.elements ≠ []) :
      FallbackParameterValidationOrdinaryParses parameters input input

/-- Exact ordinary fallback success, including retained invalid parameters,
their diagnostic-only validation, fixed-order entry modifiers, and balanced
required-body recovery. -/
inductive FallbackDeclOrdinaryParses :
    Remainder → Syntax.FallbackDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterParameters afterValidation afterModifiers
        output : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .fallbackKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (validationParsed : FallbackParameterValidationOrdinaryParses parameters
        afterParameters afterValidation)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterValidation
        payableMarker afterModifiers)
      (bodyParsed : IsolatedCoreBlockPublicOrdinaryParses .require
        afterModifiers body output) :
      FallbackDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan body.span
        value := { parameters, payableMarker, body }
      } output

/-- Exact first rejecting stage of an ordinary fallback attempt.  Parameter
validation and entry modifiers cannot reject, so only the marker, parameter
list, or uncaptured required body can reject. -/
inductive FallbackDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw)) :
      FallbackDeclRejects input input
  | parametersRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .fallbackKw)
        input markerSpan afterMarker)
      (parametersRejected : FunctionParametersRejects afterMarker rejected) :
      FallbackDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterParameters afterValidation afterModifiers
        rejected : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .fallbackKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (validationParsed : FallbackParameterValidationOrdinaryParses parameters
        afterParameters afterValidation)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterValidation
        payableMarker afterModifiers)
      (bodyRejected : IsolatedCoreBlockPublicRejects .require afterModifiers
        rejected) :
      FallbackDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberCoreOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for attribute-free contract-member
dispatch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact current-token evidence for one contract-member dispatch selector. -/
def ContractMemberCoreTokenPresentAt (input : Remainder)
    (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Exact broad success of attribute-free contract-member dispatch in
executable priority order. -/
inductive ContractMemberCoreOrdinaryParses :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | field {input output : Remainder}
      {declaration : Syntax.ContractField}
      (fieldPresent : ContractFieldStartsAt input)
      (fieldParsed : ContractFieldOrdinaryParses
        CoreExpressionOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .field declaration
      } output
  | function {input output : Remainder}
      {declaration : Syntax.FunctionDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .functionKw))
      (functionParsed : FunctionDeclOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .function declaration
      } output
  | constructor {input output : Remainder}
      {declaration : Syntax.ConstructorDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .constructorKw))
      (constructorParsed : ConstructorDeclOrdinaryParses input declaration
        output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .constructor declaration
      } output
  | fallback {input output : Remainder}
      {declaration : Syntax.FallbackDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .fallbackKw))
      (fallbackParsed : FallbackDeclOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .fallback declaration
      } output
  | typeAlias {input output : Remainder}
      {declaration : Syntax.TypeAliasDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typePresent : ContractMemberCoreTokenPresentAt input
        (.keyword .typeKw))
      (typeParsed : TypeAliasDeclOrdinaryParses input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .typeAlias declaration
      } output
  | enum {input output : Remainder} {declaration : Syntax.EnumDecl}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (enumPresent : ContractMemberCoreTokenPresentAt input
        (.identifier ContextualKeyword.enum.spelling))
      (enumParsed : EnumDeclOrdinaryParses none input declaration output) :
      ContractMemberCoreOrdinaryParses input {
        span := declaration.span
        leadingComments := []
        value := .enum declaration
      } output

/-- Exact selected branch and final remainder of an attribute-free member
rejection. -/
inductive ContractMemberCoreRejects : Remainder → Remainder → Prop where
  | fieldRejected {input rejected : Remainder}
      (fieldPresent : ContractFieldStartsAt input)
      (fieldRejected : ContractFieldRejects
        CoreExpressionOrdinaryParses CoreExpressionPublicRejects input
          rejected) :
      ContractMemberCoreRejects input rejected
  | functionRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .functionKw))
      (functionRejected : FunctionDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | constructorRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .constructorKw))
      (constructorRejected : ConstructorDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | fallbackRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackPresent : ContractMemberCoreTokenPresentAt input
        (.keyword .fallbackKw))
      (fallbackRejected : FallbackDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | typeAliasRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typePresent : ContractMemberCoreTokenPresentAt input
        (.keyword .typeKw))
      (typeRejected : TypeAliasDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | enumRejected {input rejected : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (enumPresent : ContractMemberCoreTokenPresentAt input
        (.identifier ContextualKeyword.enum.spelling))
      (enumRejected : EnumDeclRejects input rejected) :
      ContractMemberCoreRejects input rejected
  | unrecognized {input : Remainder}
      (fieldAbsent : ¬ ContractFieldStartsAt input)
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (constructorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw))
      (fallbackAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .fallbackKw))
      (typeAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .typeKw))
      (enumAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling)) :
      ContractMemberCoreRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberRecoveryOutcomeGrammar
/-!
Parser-independent exact ordinary outcomes for contract-member recovery.
Recovery consumes one mandatory token, scans up to the next member boundary,
and returns an error member without consuming that boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nonconsuming boundaries recognized by contract-member recovery. -/
inductive ContractMemberRecoveryBoundaryStartsAt : Remainder → Prop where
  | hash {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input (.symbol .hash)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | function {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.keyword .functionKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | constructor {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.keyword .constructorKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | fallback {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.keyword .fallbackKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | typeAlias {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input (.keyword .typeKw)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | rightBrace {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.symbol .rightBrace)) :
      ContractMemberRecoveryBoundaryStartsAt input
  | enum {input : Remainder}
      (present : ContractMemberCoreTokenPresentAt input
        (.identifier ContextualKeyword.enum.spelling)) :
      ContractMemberRecoveryBoundaryStartsAt input

/-- Exact stops of the scan after recovery consumed its mandatory first
token.  A missing carrier slot inside the active window finishes recovery. -/
inductive ContractMemberRecoveryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ContractMemberRecoveryStops input
  | boundary {input : Remainder}
      (starts : ContractMemberRecoveryBoundaryStartsAt input) :
      ContractMemberRecoveryStops input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ContractMemberRecoveryStops input

/-- Canonical error member produced from the first and last consumed spans. -/
def recoveredContractMemberValue
    (first last : SourceSpan) : Syntax.ContractMember := {
  span := SourceSpan.cover first last
  leadingComments := []
  value := .error
}

/-- Exact priority-ordered scan after the mandatory first recovery token. -/
inductive ContractMemberRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.ContractMember → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : ContractMemberRecoveryStops input) :
      ContractMemberRecoveryScanParses first last input
        (recoveredContractMemberValue first last) input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {member : Syntax.ContractMember}
      (continues : ¬ ContractMemberRecoveryStops input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : ContractMemberRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } member output) :
      ContractMemberRecoveryScanParses first last input member output

/-- Successful recovery consumes one arbitrary current token before scanning. -/
inductive ContractMemberRecoveryParses :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {member : Syntax.ContractMember}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : ContractMemberRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } member output) :
      ContractMemberRecoveryParses input member output

/-- Recovery rejects only when its mandatory first token is unavailable. -/
inductive ContractMemberRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ContractMemberRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ContractMemberRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeGrammar
/-!
Parser-independent broad ordinary outcomes for public contract-member dispatch.
The leading-hash branch commits to public derive parsing before parsing and
transforming one core member.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact public contract-member success, including pure derive attachment.
The attachment step does not change the core parser's final remainder. -/
inductive ContractMemberOrdinaryParses :
    Remainder → Syntax.ContractMember → Remainder → Prop where
  | plain {input output : Remainder} {member : Syntax.ContractMember}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (coreParsed : ContractMemberCoreOrdinaryParses input member output) :
      ContractMemberOrdinaryParses input member output
  | derived {input afterDerive output : Remainder}
      {derive : Syntax.DeriveAttribute}
      {coreMember member : Syntax.ContractMember}
      (hashPresent : ContractMemberCoreTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (coreParsed : ContractMemberCoreOrdinaryParses afterDerive coreMember
        output)
      (attached : ContractDeriveAttaches derive coreMember member) :
      ContractMemberOrdinaryParses input member output

/-- Exact first rejecting stage of public contract-member dispatch.  Pure
attachment has no rejecting outcome. -/
inductive ContractMemberRejects : Remainder → Remainder → Prop where
  | plainCoreRejected {input rejected : Remainder}
      (hashAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .hash))
      (coreRejected : ContractMemberCoreRejects input rejected) :
      ContractMemberRejects input rejected
  | deriveRejected {input rejected : Remainder}
      (hashPresent : ContractMemberCoreTokenPresentAt input (.symbol .hash))
      (deriveRejected : DeriveAttributeRejects input rejected) :
      ContractMemberRejects input rejected
  | derivedCoreRejected {input afterDerive rejected : Remainder}
      {derive : Syntax.DeriveAttribute}
      (hashPresent : ContractMemberCoreTokenPresentAt input (.symbol .hash))
      (deriveParsed : DeriveAttributeOrdinaryParses input derive afterDerive)
      (coreRejected : ContractMemberCoreRejects afterDerive rejected) :
      ContractMemberRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractBodyOutcomeGrammar
/-!
Broad ordinary outcomes for contract bodies.  The member loop preserves source
order, rewinds a rejected member to its original cursor, and recovers only when
that cursor is not a declaration boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A rejected derive-aware member retains its failed cursor while preserving
the token carrier and active window needed for the body-loop rewind. -/
def ContractMemberRejectsWithPreservedWindow (input : Remainder) : Prop :=
  ∃ failed, ContractMemberRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Forward-order contract members ending at the exact closing brace.

The closing branch has priority.  Otherwise a member either succeeds with
strict progress, or its window-preserving rejection is rewound and recovered
from the original cursor when no recovery boundary is present. -/
inductive ContractMemberTailOrdinaryParses :
    Remainder → List Syntax.ContractMember → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      ContractMemberTailOrdinaryParses input [] closingSpan output
  | direct {input afterMember output : Remainder}
      {member : Syntax.ContractMember} {members : List Syntax.ContractMember}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberParsed : ContractMemberOrdinaryParses input member afterMember)
      (progress : input.cursor < afterMember.cursor)
      (tail : ContractMemberTailOrdinaryParses afterMember members
        closingSpan output) :
      ContractMemberTailOrdinaryParses input (member :: members) closingSpan
        output
  | recovered {input afterRecovery output : Remainder}
      {member : Syntax.ContractMember} {members : List Syntax.ContractMember}
      {closingSpan : SourceSpan}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ContractMemberRecoveryBoundaryStartsAt input)
      (recoveryParsed : ContractMemberRecoveryParses input member
        afterRecovery)
      (tail : ContractMemberTailOrdinaryParses afterRecovery members
        closingSpan output) :
      ContractMemberTailOrdinaryParses input (member :: members) closingSpan
        output

/-- Single-output adapter retaining the closing span and forward members. -/
def ContractMemberTailOrdinaryOutcomeParses (input : Remainder)
    (tail : SourceSpan × List Syntax.ContractMember)
    (output : Remainder) : Prop :=
  ContractMemberTailOrdinaryParses input tail.2 tail.1 output

/-- Exact first rejection of the prioritized contract-member body loop. -/
inductive ContractMemberTailRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor) :
      ContractMemberTailRejects input input
  | memberAtBoundary {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryPresent : ContractMemberRecoveryBoundaryStartsAt input) :
      ContractMemberTailRejects input input
  | recoveryRejected {input rejected : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ContractMemberRecoveryBoundaryStartsAt input)
      (rejectedRecovery : ContractMemberRecoveryRejects input rejected) :
      ContractMemberTailRejects input rejected
  | laterDirect {input afterMember rejected : Remainder}
      {member : Syntax.ContractMember}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberParsed : ContractMemberOrdinaryParses input member afterMember)
      (progress : input.cursor < afterMember.cursor)
      (tailRejected : ContractMemberTailRejects afterMember rejected) :
      ContractMemberTailRejects input rejected
  | laterRecovered {input afterRecovery rejected : Remainder}
      {member : Syntax.ContractMember}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (inside : input.cursor < input.endIndex)
      (memberRejected : ContractMemberRejectsWithPreservedWindow input)
      (boundaryAbsent : ¬ ContractMemberRecoveryBoundaryStartsAt input)
      (recoveryParsed : ContractMemberRecoveryParses input member
        afterRecovery)
      (tailRejected : ContractMemberTailRejects afterRecovery rejected) :
      ContractMemberTailRejects input rejected

/-- Exact braces, covered span, and source-order broad contract members. -/
inductive ContractBodyOrdinaryParses :
    Remainder → SourceSpan → List Syntax.ContractMember →
      Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {members : List Syntax.ContractMember}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (membersParsed : ContractMemberTailOrdinaryParses afterOpening members
        closingSpan output) :
      ContractBodyOrdinaryParses input
        (SourceSpan.cover openingSpan closingSpan) members output

/-- Single-output adapter retaining the body span and forward members. -/
def ContractBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.ContractMember)
    (output : Remainder) : Prop :=
  ContractBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of the opening brace or the subsequent member loop. -/
inductive ContractBodyRejects : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      ContractBodyRejects input input
  | tailRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (tailRejected : ContractMemberTailRejects afterOpening rejected) :
      ContractBodyRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeContractDeclarationOutcomeGrammar
/-! Parser-independent broad ordinary outcomes for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad contract declaration success in executable stage order. -/
inductive ContractDeclOrdinaryParses :
    Remainder → Syntax.ContractDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterName afterGenerics output : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      {bodySpan : SourceSpan} {members : List Syntax.ContractMember}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : OptionalGenericParametersParses
        afterName genericParameters afterGenerics)
      (bodyParsed : ContractBodyOrdinaryParses afterGenerics bodySpan members
        output) :
      ContractDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := { name, genericParameters, bodySpan, members }
      } output

/-- Exact first rejecting stage of one broad contract declaration attempt. -/
inductive ContractDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .contractKw)) :
      ContractDeclRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      ContractDeclRejects input rejected
  | genericsRejected
      {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsRejected : OptionalGenericParametersRejects afterName
        rejected) :
      ContractDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterName afterGenerics rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : OptionalGenericParametersParses
        afterName genericParameters afterGenerics)
      (bodyRejected : ContractBodyRejects afterGenerics rejected) :
      ContractDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end
