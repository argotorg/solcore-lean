import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary success and exact rejection traces for Core types.

The successful relation is the existing recursive `TypeExprParses` grammar.
Rejection is indexed by executable recursion fuel; each successor layer retains
the dispatcher's branch priority and delegates recursive failures to the
preceding layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary Core-type success is the established recursive token grammar. -/
abbrev TypeExprOrdinaryParses := TypeExprParses

/-- Exact rejection while consuming the dotted tail of a qualified name. -/
inductive TypeQualifiedNameTailRejects : Remainder → Remainder → Prop where
  | componentRejected {input afterDot rejected : Remainder}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (componentRejected : IdentifierRejects afterDot rejected) :
      TypeQualifiedNameTailRejects input rejected
  | laterRejected {input afterDot afterComponent rejected : Remainder}
      {component : Syntax.Identifier} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (componentParsed : IdentifierParses afterDot component afterComponent)
      (laterRejected : TypeQualifiedNameTailRejects afterComponent rejected) :
      TypeQualifiedNameTailRejects input rejected

/-- Exact rejection of the nonempty qualified name prefix of a named type. -/
inductive TypeQualifiedNameRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : IdentifierRejects input rejected) :
      TypeQualifiedNameRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier}
      (firstParsed : IdentifierParses input first afterFirst)
      (tailRejected : TypeQualifiedNameTailRejects afterFirst rejected) :
      TypeQualifiedNameRejects input rejected

/-- Exact rejection after a positive `returns` guard. -/
inductive FunctionTypeReturnsRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | valuesRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.returns.spelling)
        input markerSpan afterMarker)
      (valuesRejected : DelimitedListRejects .leftParen .rightParen true true
        TypeExprParses nestedRejects afterMarker rejected) :
      FunctionTypeReturnsRejects nestedRejects input rejected

/-- Exact rejection of a selected `function` type branch. -/
inductive FunctionTypeRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | parametersRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (parametersRejected : DelimitedListRejects .leftParen .rightParen
        true true TypeExprParses nestedRejects afterKeyword rejected) :
      FunctionTypeRejects nestedRejects input rejected
  | returnsRejected {input afterKeyword afterParameters rejected : Remainder}
      {parameters : DelimitedList Syntax.TypeExpr} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .functionKw)
        input keywordSpan afterKeyword)
      (parametersParsed : TrailingDelimitedListParses .leftParen .rightParen
        TypeExprParses afterKeyword parameters afterParameters)
      (returnsRejected : FunctionTypeReturnsRejects nestedRejects
        afterParameters rejected) :
      FunctionTypeRejects nestedRejects input rejected

/-- Exact rejection of a selected `comptime<...>` type branch. -/
inductive ComptimeTypeRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | innerRejected {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling)
        input markerSpan afterMarker)
      (openingParsed : ExactTokenParses (.symbol .less)
        afterMarker openingSpan afterOpening)
      (innerRejected : nestedRejects afterOpening rejected) :
      ComptimeTypeRejects nestedRejects input rejected
  | closingMissing {input afterMarker afterOpening afterInner : Remainder}
      {inner : Syntax.TypeExpr} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling)
        input markerSpan afterMarker)
      (openingParsed : ExactTokenParses (.symbol .less)
        afterMarker openingSpan afterOpening)
      (innerParsed : TypeExprParses afterOpening inner afterInner)
      (closingAbsent : TokenKindAbsentAt afterInner.tokens afterInner.endIndex
        afterInner.cursor (.symbol .greater)) :
      ComptimeTypeRejects nestedRejects input afterInner

/-- Exact rejection of a selected canonical `mapping(...)` type branch. -/
inductive MappingTypeRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | keyRejected {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.mapping.spelling)
        input markerSpan afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen)
        afterMarker openingSpan afterOpening)
      (keyRejected : nestedRejects afterOpening rejected) :
      MappingTypeRejects nestedRejects input rejected
  | arrowMissing {input afterMarker afterOpening afterKey : Remainder}
      {key : Syntax.TypeExpr} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.mapping.spelling)
        input markerSpan afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen)
        afterMarker openingSpan afterOpening)
      (keyParsed : TypeExprParses afterOpening key afterKey)
      (arrowAbsent : TokenKindAbsentAt afterKey.tokens afterKey.endIndex
        afterKey.cursor (.symbol .fatArrow)) :
      MappingTypeRejects nestedRejects input afterKey
  | valueRejected
      {input afterMarker afterOpening afterKey afterArrow rejected : Remainder}
      {key : Syntax.TypeExpr} (markerSpan openingSpan arrowSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.mapping.spelling)
        input markerSpan afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen)
        afterMarker openingSpan afterOpening)
      (keyParsed : TypeExprParses afterOpening key afterKey)
      (arrowParsed : ExactTokenParses (.symbol .fatArrow)
        afterKey arrowSpan afterArrow)
      (valueRejected : nestedRejects afterArrow rejected) :
      MappingTypeRejects nestedRejects input rejected
  | closingMissing
      {input afterMarker afterOpening afterKey afterArrow afterValue : Remainder}
      {key value : Syntax.TypeExpr}
      (markerSpan openingSpan arrowSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.mapping.spelling)
        input markerSpan afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen)
        afterMarker openingSpan afterOpening)
      (keyParsed : TypeExprParses afterOpening key afterKey)
      (arrowParsed : ExactTokenParses (.symbol .fatArrow)
        afterKey arrowSpan afterArrow)
      (valueParsed : TypeExprParses afterArrow value afterValue)
      (closingAbsent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex
        afterValue.cursor (.symbol .rightParen)) :
      MappingTypeRejects nestedRejects input afterValue

/-- Exact rejection of a selected proxy type branch. -/
inductive ProxyTypeRejects (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | innerRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at)
        input markerSpan afterMarker)
      (innerRejected : nestedRejects afterMarker rejected) :
      ProxyTypeRejects nestedRejects input rejected

/-- Exact rejection of a positively selected tuple type branch. -/
inductive TupleTypeRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | selected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen)
        input openingSpan afterOpening)
      (valuesRejected : DelimitedListRejects .leftParen .rightParen true true
        TypeExprParses nestedRejects input rejected) :
      TupleTypeRejects nestedRejects input rejected

/-- Exact rejection inside the positively selected named-type argument list. -/
inductive NamedTypeArgumentsRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | selected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .less)
        input openingSpan afterOpening)
      (valuesRejected : DelimitedListRejects .less .greater false true
        TypeExprParses nestedRejects input rejected) :
      NamedTypeArgumentsRejects nestedRejects input rejected

/-- Exact rejection after a successfully parsed named-type prefix. -/
inductive NamedTypeRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | nameRejected {input rejected : Remainder}
      (nameRejected : TypeQualifiedNameRejects input rejected) :
      NamedTypeRejects nestedRejects input rejected
  | argumentsRejected {input afterName rejected : Remainder}
      {name : Syntax.QualifiedName}
      (nameParsed : QualifiedNameParses input name afterName)
      (argumentsRejected : NamedTypeArgumentsRejects nestedRejects
        afterName rejected) :
      NamedTypeRejects nestedRejects input rejected

/-- One successor-fuel layer of the prioritized Core-type dispatcher. -/
inductive TypeExprCoreRejects
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | function {input rejected : Remainder}
      (branchRejected : FunctionTypeRejects nestedRejects input rejected) :
      TypeExprCoreRejects nestedRejects input rejected
  | comptime {input rejected : Remainder}
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (branchRejected : ComptimeTypeRejects nestedRejects input rejected) :
      TypeExprCoreRejects nestedRejects input rejected
  | mapping {input rejected : Remainder}
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (branchRejected : MappingTypeRejects nestedRejects input rejected) :
      TypeExprCoreRejects nestedRejects input rejected
  | proxy {input rejected : Remainder}
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (branchRejected : ProxyTypeRejects nestedRejects input rejected) :
      TypeExprCoreRejects nestedRejects input rejected
  | tuple {input rejected : Remainder}
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (branchRejected : TupleTypeRejects nestedRejects input rejected) :
      TypeExprCoreRejects nestedRejects input rejected
  | named {input rejected : Remainder}
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (identifierPresent : ∃ span text,
        TokenAt input.tokens input.endIndex input.cursor {
          span
          value := .identifier text
        })
      (branchRejected : NamedTypeRejects nestedRejects input rejected) :
      TypeExprCoreRejects nestedRejects input rejected
  | final {input : Remainder}
      (functionAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .functionKw))
      (comptimeAbsent : ContextualSymbolPairAbsentAt input .comptime .less)
      (mappingAbsent : ContextualSymbolPairAbsentAt input .mapping .leftParen)
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (identifierAbsent : IdentifierAbsentAt input) :
      TypeExprCoreRejects nestedRejects input input

/-- Exact type-expression rejection at executable recursion fuel. -/
def TypeExprRejectsWithFuel : Nat → Remainder → Remainder → Prop
  | 0 => fun _ _ => False
  | fuel + 1 => TypeExprCoreRejects (TypeExprRejectsWithFuel fuel)

@[simp] theorem TypeExprRejectsWithFuel.zero_iff {input rejected : Remainder} :
    ¬ TypeExprRejectsWithFuel 0 input rejected := by
  simp [TypeExprRejectsWithFuel]

@[simp] theorem TypeExprRejectsWithFuel.succ_iff {fuel : Nat}
    {input rejected : Remainder} :
    TypeExprRejectsWithFuel (fuel + 1) input rejected ↔
      TypeExprCoreRejects (TypeExprRejectsWithFuel fuel) input rejected := by
  rfl

/-- Fuel selected by the public executable type parser. -/
def typeExprPublicFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 1

/-- Exact rejection relation of the public Core-type parser. -/
def TypeExprRejects (input rejected : Remainder) : Prop :=
  TypeExprRejectsWithFuel (typeExprPublicFuel input) input rejected

end Solcore.Syntax.DeclarativeGrammar
