import Solcore.Syntax.DeclarativeCoreLambdaGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for the guarded Core lambda-expression
branch.  Subordinate parameter, type, and block outcomes are supplied by the
surrounding recursive layer, so diagnosed successes remain explicit there.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional `-> Type` success over a supplied type relation. -/
inductive OptionalLambdaReturnTypeOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Option Syntax.TypeExpr → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input none input
  | present {input afterArrow output : Remainder} {type : Syntax.TypeExpr}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (typeParsed : typeOrdinary afterArrow type output) :
      OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input (some type)
        output

/-- Exact rejection after the optional-return parser commits to a present
arrow. -/
inductive OptionalLambdaReturnTypeRejects
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | typeRejected {input afterArrow rejected : Remainder}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (typeRejected : typeRejects afterArrow rejected) :
      OptionalLambdaReturnTypeRejects typeOrdinary typeRejects input rejected

/-- Ordinary guarded lambda success over supplied parameter, return-type,
and body relations. -/
inductive LambdaExpressionOrdinaryParses
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (blockOrdinary : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterMarker afterParameters afterReturn output : Remainder}
      {parameters : DelimitedList Syntax.LambdaParameter}
      {returnType : Option Syntax.TypeExpr} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersParsed : TrailingDelimitedListParses .leftParen .rightParen
        parameterOrdinary afterMarker parameters afterParameters)
      (returnTypeParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary
        afterParameters returnType afterReturn)
      (bodyParsed : blockOrdinary afterReturn body output) :
      LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
        blockOrdinary input {
          span := SourceSpan.cover markerSpan body.span
          value := .lambda markerSpan parameters returnType body
        } output

/-- Exact rejection within the guarded lambda branch, ordered by parameters,
optional return type, then body.  Marker absence belongs to the enclosing
atom dispatcher's failed lambda guard. -/
inductive LambdaExpressionRejects
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (parameterRejects : Remainder → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects blockRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | parametersRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersRejected : DelimitedListRejects .leftParen .rightParen true
        true parameterOrdinary parameterRejects afterMarker rejected) :
      LambdaExpressionRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects input rejected
  | returnTypeRejected
      {input afterMarker afterParameters rejected : Remainder}
      {parameters : DelimitedList Syntax.LambdaParameter}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersParsed : TrailingDelimitedListParses .leftParen .rightParen
        parameterOrdinary afterMarker parameters afterParameters)
      (returnTypeRejected : OptionalLambdaReturnTypeRejects typeOrdinary
        typeRejects afterParameters rejected) :
      LambdaExpressionRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects input rejected
  | bodyRejected
      {input afterMarker afterParameters afterReturn rejected : Remainder}
      {parameters : DelimitedList Syntax.LambdaParameter}
      {returnType : Option Syntax.TypeExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersParsed : TrailingDelimitedListParses .leftParen .rightParen
        parameterOrdinary afterMarker parameters afterParameters)
      (returnTypeParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary
        afterParameters returnType afterReturn)
      (bodyRejected : blockRejects afterReturn rejected) :
      LambdaExpressionRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
